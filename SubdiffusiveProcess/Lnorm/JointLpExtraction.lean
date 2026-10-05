module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import SubdiffusiveProcess.ResponseMoments.QueueHelpers
public import SubdiffusiveProcess.Compactness.OperatorLimits

@[expose] public section

/-!
This module turns compactness of countably many real-valued families in `L¹` into one
almost-surely convergent subsequence, optionally refining a prescribed subsequence. It does not
construct response compactness or identify any limiting operator.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace SubdiffusiveProcess.Lnorm

/-- A real-valued random sequence has the specified almost-sure cluster value. -/
def IsAECluster {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (L : Ω → ℝ) : Prop :=
  ∃ δ : ℕ → ℕ, StrictMono δ ∧
    ∀ᵐ ω ∂μ, Tendsto (fun n => X (δ n) ω) atTop (𝓝 (L ω))

/-- Subsequence compactness and almost-sure uniqueness give one common cluster value before
the input subsequence is chosen. -/
theorem common_ae_cluster_of_subseq_compact_unique {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hcompact : ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ δ : ℕ → ℕ, StrictMono δ ∧ ∃ L : Ω → ℝ,
        ∀ᵐ ω ∂μ, Tendsto (fun n => X (ψ (δ n)) ω) atTop (𝓝 (L ω)))
    (hunique : ∀ L S : Ω → ℝ,
      IsAECluster μ X L → IsAECluster μ X S → L =ᵐ[μ] S) :
    ∃ R : Ω → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ δ : ℕ → ℕ, StrictMono δ ∧
        ∀ᵐ ω ∂μ, Tendsto (fun n => X (ψ (δ n)) ω) atTop (𝓝 (R ω)) := by
  obtain ⟨δ₀, hδ₀, R, hR⟩ := hcompact id strictMono_id
  have hRCluster : IsAECluster μ X R := by
    refine ⟨δ₀, hδ₀, ?_⟩
    simpa only [id_eq] using hR
  refine ⟨R, ?_⟩
  intro ψ hψ
  obtain ⟨δ, hδ, S, hS⟩ := hcompact ψ hψ
  have hSCluster : IsAECluster μ X S := by
    refine ⟨ψ ∘ δ, hψ.comp hδ, ?_⟩
    filter_upwards [hS] with ω hω
    simpa only [Function.comp_apply] using hω
  have hRS : R =ᵐ[μ] S := hunique R S hRCluster hSCluster
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hS, hRS] with ω hω hEq
  simpa only [hEq] using hω

/-- Compactness of an `L¹` range gives an `L¹`-convergent subsubsequence. -/
theorem lp_subseq_of_compact_closure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hmem : ∀ n, MemLp (X n) 1 μ)
    (hcompact : IsCompact (closure (Set.range (fun n => (hmem n).toLp (X n)))))
    (ψ : ℕ → ℕ) :
    ∃ G : ↥(Lp ℝ 1 μ), ∃ τ : ℕ → ℕ, StrictMono τ ∧
      Tendsto (fun n => (hmem (ψ (τ n))).toLp (X (ψ (τ n)))) atTop (𝓝 G) := by
  let : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  let F : ℕ → Lp ℝ 1 μ := fun n => (hmem n).toLp (X n)
  have hFcompact : IsCompact (closure (Set.range (fun n => F (ψ n)))) := by
    have hsub : closure (Set.range (fun n => F (ψ n))) ⊆ closure (Set.range F) :=
      closure_minimal (s := Set.range (fun n => F (ψ n)))
        (t := closure (Set.range F)) (by
          rintro x ⟨n, rfl⟩
          exact subset_closure ⟨ψ n, rfl⟩) isClosed_closure
    exact hcompact.of_isClosed_subset isClosed_closure hsub
  have hmemF : ∀ n, F (ψ n) ∈ closure (Set.range (fun n => F (ψ n))) := fun n =>
    subset_closure ⟨n, rfl⟩
  obtain ⟨G, -, τ, hτ, hG⟩ := hFcompact.tendsto_subseq hmemF
  exact ⟨G, τ, hτ, hG⟩

/-- `L¹` convergence gives an almost-surely convergent subsubsequence. -/
theorem ae_subseq_of_lp_tendsto {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hmem : ∀ n, MemLp (X n) 1 μ)
    (G : ↥(Lp ℝ 1 μ))
    (hG : Tendsto (fun n => (hmem n).toLp (X n)) atTop (𝓝 G)) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X (τ n) ω) atTop (𝓝 ((↑↑G : Ω → ℝ) ω)) := by
  let : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  let Y : ℕ → Ω → ℝ := fun n => ↑↑((hmem n).toLp (X n))
  let Ylim : Ω → ℝ := ↑↑G
  have hnorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n => (hmem n).toLp (X n)) G).mp hG
  obtain ⟨τ, hτ, hAE⟩ :=
    _root_.SubdiffusiveProcess.ResponseMoments.exists_ae_subseq_of_eLpNorm_tendsto Ω μ Y Ylim 1
      (by norm_num) (fun n => (Lp.memLp ((hmem n).toLp (X n))).aestronglyMeasurable)
      (Lp.memLp G).aestronglyMeasurable hnorm
  have hrep : ∀ᵐ ω ∂μ, ∀ n, X n ω = Y n ω := by
    rw [ae_all_iff]
    intro n
    exact ((hmem n).coeFn_toLp).symm
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hAE, hrep] with ω hω hωrep
  have heq : (fun n => X (τ n) ω) = fun n => Y (τ n) ω := by
    funext n
    exact hωrep (τ n)
  rw [heq]
  exact hω

/-- An `L¹`-compact real-valued sequence has an almost-surely convergent subsubsequence. -/
theorem ae_subseq_of_l1_compact {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hmem : ∀ n, MemLp (X n) 1 μ)
    (hcompact : IsCompact (closure (Set.range (fun n => (hmem n).toLp (X n)))))
    (ψ : ℕ → ℕ) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L : Ω → ℝ,
      ∀ᵐ ω ∂μ, Tendsto (fun n => X (ψ (τ n)) ω) atTop (𝓝 (L ω)) := by
  obtain ⟨G, τ, hτ, hG⟩ := lp_subseq_of_compact_closure μ X hmem hcompact ψ
  obtain ⟨υ, hυ, hAE⟩ := ae_subseq_of_lp_tendsto μ
    (fun n => X (ψ (τ n))) (fun n => hmem (ψ (τ n))) G hG
  refine ⟨τ ∘ υ, hτ.comp hυ, (↑↑G : Ω → ℝ), ?_⟩
  filter_upwards [hAE] with ω hω
  simpa only [Function.comp_apply] using hω

/-- A countable family of subsequential limits can be realized along one sequence. -/
theorem ae_diagonal_countable {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hcompact : ∀ i : ℕ, ∀ σ : ℕ → ℕ, StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L : Ω → ℝ,
        ∀ᵐ ω ∂μ, Tendsto (fun n => X i (σ (τ n)) ω) atTop (𝓝 (L ω))) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧ ∃ L : ℕ → Ω → ℝ,
      ∀ᵐ ω ∂μ, ∀ i : ℕ,
        Tendsto (fun n => X i (δ n) ω) atTop (𝓝 (L i ω)) := by
  classical
  choose τ hτ L hL using hcompact
  let T := {σ : ℕ → ℕ // StrictMono σ}
  let step (i : ℕ) (σ : T) : T :=
    ⟨σ.val ∘ τ i σ.val σ.property, σ.property.comp (hτ i σ.val σ.property)⟩
  let σ : ℕ → T := Nat.rec ⟨id, strictMono_id⟩ (fun i s => step i s)
  have hsucc (i n : ℕ) :
      (σ (i + 1)).val n = (σ i).val (τ i (σ i).val (σ i).property n) := rfl
  have hrange : ∀ i j : ℕ, i ≤ j → ∀ n : ℕ,
      ∃ k : ℕ, n ≤ k ∧ (σ j).val n = (σ i).val k := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun n => ⟨n, le_rfl, rfl⟩
    | succ j hij ih =>
      intro n
      obtain ⟨k, hk, heq⟩ := ih (τ j (σ j).val (σ j).property n)
      exact ⟨k, (hτ j (σ j).val (σ j).property).id_le n |>.trans hk,
        (hsucc j n).trans heq⟩
  let δ : ℕ → ℕ := fun n => (σ n).val n
  have hδ : StrictMono δ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change (σ n).val n < (σ (n + 1)).val (n + 1)
    rw [hsucc]
    exact (σ n).property (lt_of_lt_of_le (Nat.lt_succ_self n)
      ((hτ n (σ n).val (σ n).property).id_le (n + 1)))
  refine ⟨δ, hδ, fun i => L i (σ i).val (σ i).property, ?_⟩
  have hall : ∀ᵐ ω ∂μ, ∀ i : ℕ,
      Tendsto (fun n => X i ((σ (i + 1)).val n) ω) atTop
        (𝓝 (L i (σ i).val (σ i).property ω)) := by
    rw [ae_all_iff]
    intro i
    exact hL i (σ i).val (σ i).property
  filter_upwards [hall] with ω hω i
  have ht : ∀ n : ℕ, ∃ k : ℕ, n + (i + 1) ≤ k ∧
      δ (n + (i + 1)) = (σ (i + 1)).val k :=
    fun n => hrange (i + 1) (n + (i + 1)) (by omega) (n + (i + 1))
  choose κ hκ hκeq using ht
  have hκtop : Tendsto κ atTop atTop :=
    tendsto_atTop_mono (fun n => (Nat.le_add_right n (i + 1)).trans (hκ n)) tendsto_id
  apply (tendsto_add_atTop_iff_nat (i + 1)).mp
  exact ((hω i).comp hκtop).congr' (Eventually.of_forall fun n => by
    change X i ((σ (i + 1)).val (κ n)) ω = X i (δ (n + (i + 1))) ω
    rw [hκeq n])

theorem ae_subseq_of_countable_l1_compact {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hmem : ∀ i n, MemLp (X i n) 1 μ)
    (hcompact : ∀ i, IsCompact
      (closure (Set.range (fun n => (hmem i n).toLp (X i n)))) )
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L : ℕ → Ω → ℝ,
      ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => X i (ψ (τ n)) ω) atTop (𝓝 (L i ω)) := by
  classical
  have hcompact' : ∀ i, ∀ σ : ℕ → ℕ, StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L : Ω → ℝ,
        ∀ᵐ ω ∂μ, Tendsto (fun n => X i (σ (τ n)) ω) atTop (𝓝 (L ω)) := by
    intro i σ hσ
    have hcomp : IsCompact
        (closure (Set.range (fun n => (hmem i (σ n)).toLp (X i (σ n))))) := by
      have hsub :
          closure (Set.range (fun n => (hmem i (σ n)).toLp (X i (σ n)))) ⊆
            closure (Set.range (fun n => (hmem i n).toLp (X i n))) :=
        closure_minimal (s := Set.range (fun n => (hmem i (σ n)).toLp (X i (σ n))))
          (t := closure (Set.range (fun n => (hmem i n).toLp (X i n)))) (by
            rintro x ⟨n, rfl⟩
            exact subset_closure ⟨σ n, rfl⟩) isClosed_closure
      exact (hcompact i).of_isClosed_subset isClosed_closure hsub
    obtain ⟨τ, hτ, L, hL⟩ := ae_subseq_of_l1_compact μ (fun n => X i (σ n))
      (fun n => hmem i (σ n)) hcomp id
    exact ⟨τ, hτ, L, hL⟩
  obtain ⟨τ, hτ, L, hL⟩ :=
    ae_diagonal_countable μ (fun i n => X i (ψ n))
      (fun i σ hσ => by
        obtain ⟨κ, hκ, L, hL⟩ := hcompact' i (ψ ∘ σ) (hψ.comp hσ)
        exact ⟨κ, hκ, L, hL⟩)
  exact ⟨τ, hτ, L, hL⟩

/-- A countable, possibly dependent family of `L¹`-compact scalar sequences has one common
almost-surely convergent subsequence. -/
theorem ae_subseq_of_countable_l1_compact_index {Ω : Type} {ι : Type*} [MeasurableSpace Ω]
    [Countable ι] [Nonempty ι] (μ : Measure Ω) (X : ι → ℕ → Ω → ℝ)
    (hmem : ∀ i n, MemLp (X i n) 1 μ)
    (hcompact : ∀ i, IsCompact
      (closure (Set.range (fun n => (hmem i n).toLp (X i n)))))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L : ι → Ω → ℝ,
      ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => X i (ψ (τ n)) ω) atTop (𝓝 (L i ω)) := by
  classical
  obtain ⟨enum, henum⟩ := exists_surjective_nat ι
  obtain ⟨τ, hτ, L, hL⟩ := ae_subseq_of_countable_l1_compact μ
    (fun i n => X (enum i) n) (fun i n => hmem (enum i) n)
    (fun i => hcompact (enum i)) ψ hψ
  choose index hindex using henum
  refine ⟨τ, hτ, fun i => L (index i), ?_⟩
  filter_upwards [hL] with ω hω i
  simpa only [hindex i] using hω (index i)

/-- A countable family with subsequential compactness along every reindexing has one common
almost-sure extraction. -/
theorem ae_diagonal_countable_subseq_index {Ω : Type} {ι : Type*} [MeasurableSpace Ω]
    [Countable ι] [Nonempty ι] (μ : Measure Ω) (X : ι → ℕ → Ω → ℝ)
    (hsubseq : ∀ (i : ι) (σ : ℕ → ℕ), StrictMono σ →
      ∃ (τ : ℕ → ℕ), StrictMono τ ∧ ∃ L : Ω → ℝ,
        ∀ᵐ ω ∂μ, Tendsto (fun n => X i (σ (τ n)) ω) atTop (𝓝 (L ω)))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧ ∃ L : ι → Ω → ℝ,
      ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => X i (ψ (δ n)) ω) atTop (𝓝 (L i ω)) := by
  classical
  obtain ⟨enum, henum⟩ := exists_surjective_nat ι
  obtain ⟨δ, hδ, L, hL⟩ := ae_diagonal_countable μ
    (fun i n => X (enum i) (ψ n))
    (fun i σ hσ => hsubseq (enum i) (ψ ∘ σ) (hψ.comp hσ))
  choose index hindex using henum
  refine ⟨δ, hδ, fun i => L (index i), ?_⟩
  filter_upwards [hL] with ω hω i
  simpa only [hindex i] using hω (index i)

/-- One diagonal extraction gives operator-norm limits for a countable family once every
quadratic response is `L¹`-compact and the operator images are collectively compact. -/
theorem ae_operator_subseq_of_quadratic_l1_compact
    {Ω : Type} {ι : Type*} [MeasurableSpace Ω] [Countable ι] [Nonempty ι]
    (μ : Measure Ω)
    (H : ι → Type*) [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℝ (H i)] [∀ i, CompleteSpace (H i)]
    (T : ∀ i, ℕ → Ω → H i →L[ℝ] H i)
    (D : ∀ i, Set (H i)) (hDcount : ∀ i, Countable (D i))
    (hDdense : ∀ i, Dense (D i : Set (H i)))
    (hDadd : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, x + y ∈ D i)
    (hsym : ∀ n ω i x y, inner ℝ (T i n ω x) y = inner ℝ x (T i n ω y))
    (hpos : ∀ n ω i x, 0 ≤ inner ℝ x (T i n ω x))
    (hcollective : ∀ᵐ ω ∂μ, ∀ i,
      IsCompact (closure (⋃ n : ℕ,
        (T i n ω) '' Metric.closedBall (0 : H i) 1)))
    (hmem : ∀ i (x : D i) n,
      MemLp (fun ω => inner ℝ (x : H i) (T i n ω x)) 1 μ)
    (hcompact : ∀ i (x : D i), IsCompact (closure (Set.range (fun n =>
      (hmem i x n).toLp (fun ω => inner ℝ (x : H i) (T i n ω x))))))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧
      ∃ G : ∀ i, Ω → H i →L[ℝ] H i,
        ∀ᵐ ω ∂μ, ∀ i,
          Tendsto (fun n => T i (ψ (δ n)) ω) atTop (𝓝 (G i ω)) := by
  classical
  let ιQ := Σ i : ι, {x : H i // x ∈ D i}
  let Q : ιQ → ℕ → Ω → ℝ := fun ix n ω =>
    inner ℝ (ix.2 : H ix.1) (T ix.1 n ω ix.2)
  let : ∀ i, Countable {x : H i // x ∈ D i} := hDcount
  have : Nonempty ιQ := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    let : Nonempty (H i) := ⟨0⟩
    obtain ⟨x, hx⟩ := (hDdense i).nonempty
    exact ⟨⟨i, ⟨x, hx⟩⟩⟩
  have : Countable ιQ := by
    change Countable (Sigma fun i : ι => {x : H i // x ∈ D i})
    infer_instance
  have hQmem (ix : ιQ) (n : ℕ) : MemLp (Q ix n) 1 μ := by
    change MemLp (fun ω => inner ℝ (ix.2 : H ix.1) (T ix.1 n ω ix.2)) 1 μ
    exact hmem ix.1 ix.2 n
  have hQcompact (ix : ιQ) : IsCompact
      (closure (Set.range (fun n => (hQmem ix n).toLp (Q ix n)))) := by
    change IsCompact (closure (Set.range (fun n =>
      (hmem ix.1 ix.2 n).toLp
        (fun ω => inner ℝ (ix.2 : H ix.1) (T ix.1 n ω ix.2)))))
    exact hcompact ix.1 ix.2
  obtain ⟨δ, hδ, L, hL⟩ := ae_subseq_of_countable_l1_compact_index
    (ι := ιQ) (X := Q) μ
    hQmem hQcompact ψ hψ
  have hgood : ∀ᵐ ω ∂μ,
      (∀ i, IsCompact (closure (⋃ n : ℕ,
        (T i n ω) '' Metric.closedBall (0 : H i) 1))) ∧
      (∀ i (x : D i), CauchySeq (fun n =>
        inner ℝ (x : H i) (T i (ψ (δ n)) ω x))) := by
    filter_upwards [hcollective, hL] with ω hcoll hresp
    refine ⟨hcoll, ?_⟩
    intro i x
    have ht := hresp ⟨i, x⟩
    change Tendsto (fun n =>
      inner ℝ (x : H i) (T i (ψ (δ n)) ω x)) atTop (𝓝 (L ⟨i, x⟩ ω)) at ht
    exact ht.cauchySeq
  let good (ω : Ω) : Prop :=
    (∀ i, IsCompact (closure (⋃ n : ℕ,
      (T i n ω) '' Metric.closedBall (0 : H i) 1))) ∧
    (∀ i (x : D i), CauchySeq (fun n =>
      inner ℝ (x : H i) (T i (ψ (δ n)) ω x)))
  have hop (ω : Ω) (hg : good ω) (i : ι) :
      ∃ G : H i →L[ℝ] H i,
        Tendsto (fun n => T i (ψ (δ n)) ω) atTop (𝓝 G) := by
    have hsub : (⋃ n : ℕ, (T i (ψ (δ n)) ω) '' Metric.closedBall (0 : H i) 1) ⊆
        ⋃ n : ℕ, (T i n ω) '' Metric.closedBall (0 : H i) 1 := by
      intro v hv
      rcases Set.mem_iUnion.mp hv with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨ψ (δ n), hn⟩
    have hcompactOp : IsCompact (closure (⋃ n : ℕ,
        (T i (ψ (δ n)) ω) '' Metric.closedBall (0 : H i) 1)) :=
      (hg.1 i).of_isClosed_subset isClosed_closure
        (closure_minimal (hsub.trans subset_closure) isClosed_closure)
    obtain ⟨G, hG, -⟩ :=
      SubdiffusiveProcess.existsUnique_limit_of_collectively_compact_quadratic_responses
        (hDdense i) (hDadd i)
        (fun n x y => hsym (ψ (δ n)) ω i x y)
        (fun n x => hpos (ψ (δ n)) ω i x) hcompactOp
        (fun x hx => hg.2 i ⟨x, hx⟩)
    exact ⟨G, hG.1⟩
  let G : ∀ i, Ω → H i →L[ℝ] H i := fun i ω =>
    if hg : good ω then Classical.choose (hop ω hg i) else 0
  refine ⟨δ, hδ, G, ?_⟩
  filter_upwards [hgood] with ω hg i
  have hlim := (Classical.choose_spec (hop ω hg i))
  have hgoodω : good ω := hg
  simpa only [G, dite_eq_left hgoodω] using hlim

/-- Joint operator extraction from countably many scalar subsequential compactness inputs and
pathwise collective compactness. -/
theorem ae_operator_subseq_of_quadratic_subseq_compact
    {Ω : Type} {ι : Type*} [MeasurableSpace Ω] [Countable ι] [Nonempty ι]
    (μ : Measure Ω)
    (H : ι → Type*) [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℝ (H i)] [∀ i, CompleteSpace (H i)]
    (T : ∀ i, ℕ → Ω → H i →L[ℝ] H i)
    (D : ∀ i, Set (H i)) (hDcount : ∀ i, Countable (D i))
    (hDdense : ∀ i, Dense (D i : Set (H i)))
    (hDadd : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, x + y ∈ D i)
    (hsym : ∀ n ω i x y, inner ℝ (T i n ω x) y = inner ℝ x (T i n ω y))
    (hpos : ∀ n ω i x, 0 ≤ inner ℝ x (T i n ω x))
    (hcollective : ∀ᵐ ω ∂μ, ∀ i,
      IsCompact (closure (⋃ n : ℕ,
        (T i n ω) '' Metric.closedBall (0 : H i) 1)))
    (hresponse : ∀ i (x : D i) (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L : Ω → ℝ,
        ∀ᵐ ω ∂μ, Tendsto (fun n => inner ℝ (x : H i) (T i (σ (τ n)) ω x))
          atTop (𝓝 (L ω)))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧
      ∃ G : ∀ i, Ω → H i →L[ℝ] H i,
        ∀ᵐ ω ∂μ, ∀ i,
          Tendsto (fun n => T i (ψ (δ n)) ω) atTop (𝓝 (G i ω)) := by
  classical
  let ιQ := Σ i : ι, {x : H i // x ∈ D i}
  let Q : ιQ → ℕ → Ω → ℝ := fun ix n ω =>
    inner ℝ (ix.2 : H ix.1) (T ix.1 n ω ix.2)
  let : ∀ i, Countable {x : H i // x ∈ D i} := hDcount
  have : Nonempty ιQ := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    let : Nonempty (H i) := ⟨0⟩
    obtain ⟨x, hx⟩ := (hDdense i).nonempty
    exact ⟨⟨i, ⟨x, hx⟩⟩⟩
  have : Countable ιQ := by
    change Countable (Sigma fun i : ι => {x : H i // x ∈ D i})
    infer_instance
  let Qψ : ιQ → ℕ → Ω → ℝ := fun ix n ω => Q ix (ψ n) ω
  have hQsubseq (ix : ιQ) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L : Ω → ℝ,
        ∀ᵐ ω ∂μ, Tendsto (fun n => Qψ ix (σ (τ n)) ω) atTop (𝓝 (L ω)) := by
    obtain ⟨τ, hτ, L, hL⟩ := hresponse ix.1 ix.2 (ψ ∘ σ) (hψ.comp hσ)
    exact ⟨τ, hτ, L, hL⟩
  obtain ⟨δ, hδ, L, hL⟩ := ae_diagonal_countable_subseq_index μ Qψ hQsubseq
    id strictMono_id
  have hgood : ∀ᵐ ω ∂μ,
      (∀ i, IsCompact (closure (⋃ n : ℕ,
        (T i n ω) '' Metric.closedBall (0 : H i) 1))) ∧
      (∀ i (x : D i), CauchySeq (fun n =>
        inner ℝ (x : H i) (T i (ψ (δ n)) ω x))) := by
    filter_upwards [hcollective, hL] with ω hcoll hresp
    refine ⟨hcoll, ?_⟩
    intro i x
    have ht := hresp ⟨i, x⟩
    change Tendsto (fun n =>
      inner ℝ (x : H i) (T i (ψ (δ n)) ω x)) atTop (𝓝 (L ⟨i, x⟩ ω)) at ht
    exact ht.cauchySeq
  let good (ω : Ω) : Prop :=
    (∀ i, IsCompact (closure (⋃ n : ℕ,
      (T i n ω) '' Metric.closedBall (0 : H i) 1))) ∧
    (∀ i (x : D i), CauchySeq (fun n =>
      inner ℝ (x : H i) (T i (ψ (δ n)) ω x)))
  have hop (ω : Ω) (hg : good ω) (i : ι) :
      ∃ G : H i →L[ℝ] H i,
        Tendsto (fun n => T i (ψ (δ n)) ω) atTop (𝓝 G) := by
    have hsub : (⋃ n : ℕ, (T i (ψ (δ n)) ω) '' Metric.closedBall (0 : H i) 1) ⊆
        ⋃ n : ℕ, (T i n ω) '' Metric.closedBall (0 : H i) 1 := by
      intro v hv
      rcases Set.mem_iUnion.mp hv with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨ψ (δ n), hn⟩
    have hcompactOp : IsCompact (closure (⋃ n : ℕ,
        (T i (ψ (δ n)) ω) '' Metric.closedBall (0 : H i) 1)) :=
      (hg.1 i).of_isClosed_subset isClosed_closure
        (closure_minimal (hsub.trans subset_closure) isClosed_closure)
    obtain ⟨G, hG, -⟩ :=
      SubdiffusiveProcess.existsUnique_limit_of_collectively_compact_quadratic_responses
        (hDdense i) (hDadd i)
        (fun n x y => hsym (ψ (δ n)) ω i x y)
        (fun n x => hpos (ψ (δ n)) ω i x) hcompactOp
        (fun x hx => hg.2 i ⟨x, hx⟩)
    exact ⟨G, hG.1⟩
  let G : ∀ i, Ω → H i →L[ℝ] H i := fun i ω =>
    if hg : good ω then Classical.choose (hop ω hg i) else 0
  refine ⟨δ, hδ, G, ?_⟩
  filter_upwards [hgood] with ω hg i
  have hlim := (Classical.choose_spec (hop ω hg i))
  have hgoodω : good ω := hg
  simpa only [G, dite_eq_left hgoodω] using hlim


end SubdiffusiveProcess.Lnorm
