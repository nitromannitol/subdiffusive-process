module

public import SubdiffusiveProcess.Paper.prop_uniform_resolvent_cutoff_oscillation
public import SubdiffusiveProcess.Paper.cutoff_campanato_bound
public import SubdiffusiveProcess.Paper.prop_speed_resolvent
public import SubdiffusiveProcess.Paper.limiting_local_energy
public import SubdiffusiveProcess.Paper.speed_trace_completion
public import SubdiffusiveProcess.Paper.lem_varying_trace
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.finite_speed_resolvent_properties
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Metrizable.ContinuousMap

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace Set
open MarkovProcess
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper
open Classical

private theorem aux_prop_uniform_resolvent_subsequence_bridge_measurable_contmap_of_eval
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [SeparableSpace X] [Nonempty X] [MeasurableSpace C(X, ℝ)]
    [BorelSpace C(X, ℝ)] [PolishSpace C(X, ℝ)]
    (F : Ω → C(X, ℝ))
    (hF : ∀ x : X, Measurable (fun ω => F ω x)) : Measurable F := by
  let q : ℕ → X := TopologicalSpace.denseSeq X
  let e : C(X, ℝ) → (ℕ → ℝ) := fun g n => g (q n)
  have hecont : Continuous e := by
    apply continuous_pi
    intro n
    exact continuous_eval_const (q n)
  have heinj : Function.Injective e := by
    intro g h hgh
    apply ContinuousMap.ext
    have heq : (g : X → ℝ) ∘ q = (h : X → ℝ) ∘ q := by
      funext n
      exact congrFun hgh n
    exact congrFun ((TopologicalSpace.denseRange_denseSeq X).equalizer g.continuous h.continuous heq)
  have hemb : MeasurableEmbedding e := hecont.measurableEmbedding heinj
  apply hemb.measurable_comp_iff.mp
  change Measurable (fun ω n => F ω (q n))
  exact measurable_pi_iff.mpr (fun n => hF (q n))
theorem aux_prop_uniform_resolvent_subsequence_bridge_zero_extend_continuous {d : ℕ} (K : Set (SpatialCoordinates d)) (u : SpatialCoordinates d → ℝ)
    (hK : IsClosed K) (hcont : ContinuousOn u K) (hzero : ∀ x ∈ frontier K, u x = 0) :
    Continuous (fun x => if x ∈ K then u x else 0) := by
  classical
  let g : SpatialCoordinates d → ℝ := fun x => if x ∈ K then u x else 0
  show Continuous g
  have hfK : ContinuousOn g K := by
    apply hcont.congr
    intro y hy
    change (if y ∈ K then u y else 0) = u y
    rw [ite_eq_left hy]
  have hfKc : ContinuousOn g Kᶜ := by
    have hconst : ContinuousOn (fun _ : SpatialCoordinates d => (0 : ℝ)) Kᶜ := continuousOn_const
    refine hconst.congr ?_
    intro y hy
    change (if y ∈ K then u y else 0) = 0
    rw [ite_eq_right ((mem_compl_iff K y).mp hy)]
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxK : x ∈ K
  · by_cases hxi : x ∈ interior K
    · exact hfK.continuousAt (interior_mem_nhds.mp (isOpen_interior.mem_nhds hxi))
    · have hxf : x ∈ frontier K := by
        unfold frontier
        rw [hK.closure_eq]
        exact ⟨hxK, hxi⟩
      have hux : u x = 0 := hzero x hxf
      have h1 : ContinuousWithinAt g K x := by
        refine (hcont.continuousWithinAt hxK).congr ?_ ?_
        · intro y hy
          change (if y ∈ K then u y else 0) = u y
          rw [ite_eq_left hy]
        · change (if x ∈ K then u x else 0) = u x
          rw [ite_eq_left hxK]
      have h2 : ContinuousWithinAt g Kᶜ x := by
        have hconst : ContinuousWithinAt (fun _ : SpatialCoordinates d => (0 : ℝ)) Kᶜ x :=
          continuousWithinAt_const
        refine hconst.congr ?_ ?_
        · intro y hy
          change (if y ∈ K then u y else 0) = 0
          rw [ite_eq_right ((mem_compl_iff K y).mp hy)]
        · change (if x ∈ K then u x else 0) = 0
          rw [ite_eq_left hxK, hux]
      have hunion : ContinuousWithinAt g (K ∪ Kᶜ) x := h1.union h2
      rw [union_compl_self] at hunion
      exact (continuousWithinAt_univ g x).mp hunion
  · exact hfKc.continuousAt (hK.isOpen_compl.mem_nhds hxK)

theorem aux_prop_uniform_resolvent_subsequence_bridge_eqOn_of_ae_eq {d : ℕ} (U : Set (SpatialCoordinates d)) (K : Set (SpatialCoordinates d))
    (hUopen : IsOpen U) (_hUne : U.Nonempty) (hUcl : closure U = K)
    (h g : SpatialCoordinates d → ℝ) (hh : ContinuousOn h K) (hg : ContinuousOn g K)
    (hae : h =ᵐ[volume.restrict U] g) : ∀ x ∈ K, h x = g x := by
  have hUK : U ⊆ K := hUcl ▸ subset_closure
  have hKU : K ⊆ closure U := fun x hx => by
    rw [← hUcl] at hx
    exact hx
  have hfgU : EqOn h g U := fun x hx =>
    lane2_eqOn_of_ae_eq_of_continuousOn (S := U) (f := h) (g := g) hUopen
      (hh.mono hUK) (hg.mono hUK) hae x hx
  have hK : EqOn h g K :=
    EqOn.of_subset_closure (s := U) (t := K) (f := h) (g := g) hfgU hh hg hUK hKU
  exact fun x hx => hK hx

theorem aux_prop_uniform_resolvent_subsequence_bridge_subseq_uniform_extract {d : ℕ} (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (u : ℕ → SpatialCoordinates d → ℝ) (hcont : ∀ N, ContinuousOn (u N) K)
    (hbdd : ∃ B : ℝ, ∀ N, ∀ x ∈ K, |u N x| ≤ B)
    (hC : ∃ C : ℝ, 0 ≤ C ∧ ∀ N, ∀ x ∈ K, ∀ y ∈ K, |u N x - u N y| ≤ C * dist x y ^ (1 / 4 : ℝ))
    (σ : ℕ → ℕ) (_hσ : StrictMono σ) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g K ∧
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ x ∈ K, |u (σ (τ k)) x - g x| < eps) := by
  classical
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨C, hC0, hCb⟩ := hC
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let f : ℕ → BoundedContinuousFunction ↥K ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact (ContinuousMap.mk (K.domRestrict (u n)) (ContinuousOn.domRestrict (hcont n)))
  let A : Set (BoundedContinuousFunction ↥K ℝ) := Set.range f
  have hA : ∀ (g : BoundedContinuousFunction ↥K ℝ) (x : ↥K), g ∈ A → g x ∈ Set.Icc (-B) B := by
    rintro g x ⟨n, rfl⟩
    change u n ↑x ∈ Set.Icc (-B) B
    exact abs_le.mp (hB n ↑x x.property)
  have heq : Equicontinuous ((↑) : A → ↥K → ℝ) := by
    refine Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C * t ^ (1 / 4 : ℝ)) ?_ _ ?_
    · have h0 : Tendsto (fun t : ℝ => t ^ (1 / 4 : ℝ)) (𝓝 0) (𝓝 0) := by
        have ht := (Real.continuousAt_rpow_const 0 (1 / 4) (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))).tendsto
        rwa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] at ht
      simpa using h0.const_mul C
    · intro x y i
      obtain ⟨n, hn⟩ := i.property
      have hb : |u n ↑x - u n ↑y| ≤ C * dist x y ^ (1 / 4 : ℝ) := hCb n ↑x x.property ↑y y.property
      rw [← hn]
      change dist (u n ↑x) (u n ↑y) ≤ C * dist x y ^ (1 / 4 : ℝ)
      exact le_trans (le_of_eq (Real.dist_eq _ _)) hb
  have hcomp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc (-B) B) isCompact_Icc A hA heq
  obtain ⟨a, ha, τ, hτ, htend⟩ := hcomp.tendsto_subseq (x := fun k => f (σ k)) (fun k => subset_closure ⟨σ k, rfl⟩)
  let g : SpatialCoordinates d → ℝ := fun x => if hx : x ∈ K then a ⟨x, hx⟩ else 0
  refine ⟨τ, hτ, g, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hgr : K.domRestrict g = ⇑a := by
      funext x
      change (if hx : (x : SpatialCoordinates d) ∈ K then a ⟨x, hx⟩ else 0) = a x
      exact dite_eq_left x.property
    rw [hgr]; exact a.continuous
  · intro eps heps
    obtain ⟨k0, hk0⟩ := Metric.tendsto_atTop.mp htend eps heps
    refine ⟨k0, fun k hk x hx => ?_⟩
    have hdist : dist (f (σ (τ k))) a < eps := hk0 k hk
    have hpt : dist ((f (σ (τ k))) ⟨x, hx⟩) (a ⟨x, hx⟩) ≤ dist (f (σ (τ k))) a :=
      (BoundedContinuousFunction.dist_le (f := f (σ (τ k))) (g := a)
        (C := dist (f (σ (τ k))) a) dist_nonneg).mp le_rfl ⟨x, hx⟩
    have hlt : dist ((f (σ (τ k))) ⟨x, hx⟩) (a ⟨x, hx⟩) < eps := lt_of_le_of_lt hpt hdist
    have hfx : (f (σ (τ k))) ⟨x, hx⟩ = u (σ (τ k)) x := rfl
    have hgx : g x = a ⟨x, hx⟩ := by
      change (if h : x ∈ K then a ⟨x, h⟩ else 0) = a ⟨x, hx⟩
      exact dite_eq_left hx
    rw [Real.dist_eq, hfx, ← hgx] at hlt
    exact hlt

theorem aux_prop_uniform_resolvent_subsequence_bridge_cube_frontier_near {d : ℕ} (hd : 2 ≤ d) (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (closure ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))),
        dist x y ≤ D := by
  refine ⟨Homogenization.cubeScaleFactor Qtri, le_of_lt hr, ?_⟩
  intro x hx
  set i0 : Fin d := ⟨0, by omega⟩
  set v : SpatialCoordinates d :=
    fun i => Homogenization.cubeCenter Qtri i - Homogenization.cubeScaleFactor Qtri / 2
  have hUC : closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) ⊆
      Set.pi Set.univ (fun i => Set.Icc (Homogenization.cubeCenter Qtri i - Homogenization.cubeScaleFactor Qtri / 2)
        (Homogenization.cubeCenter Qtri i + Homogenization.cubeScaleFactor Qtri / 2)) := by
    apply closure_minimal
    · intro w hw
      rw [centeredCube_eq_pi (Homogenization.cubeCenter Qtri) hr] at hw
      rw [Set.mem_pi] at hw ⊢
      intro i _
      exact Set.Ioo_subset_Icc_self (hw i (Set.mem_univ i))
    · apply isClosed_set_pi
      intro i _
      exact isClosed_Icc
  have hxC := Set.mem_pi.mp (hUC hx)
  refine ⟨v, ?_, ?_⟩
  · have hyS : v ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) := by
      rw [Metric.mem_closure_iff]
      intro eps heps
      refine ⟨fun i => v i + min eps (Homogenization.cubeScaleFactor Qtri) / 4, ?_, ?_⟩
      · rw [centeredCube_eq_pi (Homogenization.cubeCenter Qtri) hr, Set.mem_pi]
        intro i _
        rw [Set.mem_Ioo]
        constructor
        · have hδ : 0 < min eps (Homogenization.cubeScaleFactor Qtri) / 4 := by
            have h1 : 0 < min eps (Homogenization.cubeScaleFactor Qtri) := lt_min heps hr
            linarith
          dsimp only [v]
          linarith
        · have hδ : min eps (Homogenization.cubeScaleFactor Qtri) / 4 < Homogenization.cubeScaleFactor Qtri := by
            have h1 : min eps (Homogenization.cubeScaleFactor Qtri) ≤ Homogenization.cubeScaleFactor Qtri := min_le_right _ _
            linarith
          dsimp only [v]
          linarith
      · have hδpos : 0 < min eps (Homogenization.cubeScaleFactor Qtri) / 4 := by
          have h1 : 0 < min eps (Homogenization.cubeScaleFactor Qtri) := lt_min heps hr
          linarith
        have hδlt : min eps (Homogenization.cubeScaleFactor Qtri) / 4 < eps := by
          have h1 : min eps (Homogenization.cubeScaleFactor Qtri) ≤ eps := min_le_left _ _
          linarith
        have hdist : dist v (fun i => v i + min eps (Homogenization.cubeScaleFactor Qtri) / 4)
            ≤ min eps (Homogenization.cubeScaleFactor Qtri) / 4 := by
          rw [dist_pi_le_iff (le_of_lt hδpos)]
          intro i
          rw [Real.dist_eq]
          have hz : v i - (v i + min eps (Homogenization.cubeScaleFactor Qtri) / 4)
              = -(min eps (Homogenization.cubeScaleFactor Qtri) / 4) := by ring
          rw [hz, abs_neg]
          exact le_of_eq (abs_of_nonneg (le_of_lt hδpos))
        linarith
    have hyI : v ∉ interior (closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) := by
      intro hyint
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hyint
      obtain ⟨e, hepos, hesub⟩ := hyint
      have hmem : Function.update v i0 (v i0 - e / 2) ∈ Metric.ball v e := by
        rw [Metric.mem_ball]
        have hdist : dist (Function.update v i0 (v i0 - e / 2)) v ≤ e / 2 := by
          rw [dist_pi_le_iff (by linarith)]
          intro i
          rw [Real.dist_eq]
          by_cases h : i = i0
          · rw [h, Function.update_self]
            have hz : (v i0 - e / 2) - v i0 = -(e / 2) := by ring
            rw [hz, abs_neg]
            exact le_of_eq (abs_of_nonneg (by linarith))
          · rw [Function.update_of_ne h]
            have hz : v i - v i = 0 := by ring
            rw [hz, abs_zero]
            linarith
        linarith
      have hcl : Function.update v i0 (v i0 - e / 2) ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) := hesub hmem
      have hC := Set.mem_pi.mp (hUC hcl) i0 (Set.mem_univ i0)
      have hlow := (Set.mem_Icc.mp hC).1
      rw [Function.update_self] at hlow
      have hv : v i0 = Homogenization.cubeCenter Qtri i0 - Homogenization.cubeScaleFactor Qtri / 2 := rfl
      rw [hv] at hlow
      linarith
    rw [frontier_eq_closure_inter_closure, Set.mem_inter_iff, closure_closure]
    refine ⟨?_, ?_⟩
    · exact hyS
    · rw [closure_compl, Set.mem_compl_iff]
      exact hyI
  · rw [dist_pi_le_iff (le_of_lt hr)]
    intro i
    rw [Real.dist_eq]
    have hl : Homogenization.cubeCenter Qtri i - Homogenization.cubeScaleFactor Qtri / 2 ≤ x i :=
      (Set.mem_Icc.mp (hxC i (Set.mem_univ i))).1
    have hu : x i ≤ Homogenization.cubeCenter Qtri i + Homogenization.cubeScaleFactor Qtri / 2 :=
      (Set.mem_Icc.mp (hxC i (Set.mem_univ i))).2
    have hv : v i = Homogenization.cubeCenter Qtri i - Homogenization.cubeScaleFactor Qtri / 2 := rfl
    rw [hv]
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem aux_prop_uniform_resolvent_subsequence_bridge_prob_bound_from_ae {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (F : ℕ → Ω → SpatialCoordinates d → ℝ) (G : Ω → SpatialCoordinates d → ℝ)
    (hF : ∀ (N : ℕ) (x : SpatialCoordinates d), Measurable (fun ω => F N ω x))
    (hG : ∀ x : SpatialCoordinates d, Measurable (fun ω => G ω x))
    (hcont : ∀ᵐ ω ∂μ, ∀ N, ContinuousOn (F N ω) K)
    (hcontG : ∀ᵐ ω ∂μ, ContinuousOn (G ω) K)
    (hconv : ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ x ∈ K, |F N ω x - G ω x| < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      μ {ω : Ω | ∃ x ∈ K, ε ≤ |F N ω x - G ω x|} ≤ ENNReal.ofReal rho := by
  intro ε hε rho hrho
  by_cases hKne : K.Nonempty
  · have hNe : Nonempty ↥K := hKne.to_subtype
    have hCpt : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
    let dseq : ℕ → ↥K := TopologicalSpace.denseSeq ↥K
    have hdseq : DenseRange dseq := TopologicalSpace.denseRange_denseSeq ↥K
    let M : ℕ → Ω → ℝ≥0∞ := fun N ω => ⨆ n, ENNReal.ofReal |F N ω (dseq n) - G ω (dseq n)|
    have hMmeas : ∀ N, Measurable (M N) := by
      intro N
      apply Measurable.iSup
      intro n
      exact ENNReal.measurable_ofReal.comp (((hF N (dseq n)).sub (hG (dseq n))).abs)
    have hMtend : ∀ᵐ ω ∂μ, Tendsto (fun N => M N ω) atTop (𝓝 0) := by
      filter_upwards [hconv] with ω hcv
      rw [ENNReal.tendsto_atTop_zero]
      intro δ hδ
      rcases eq_or_ne δ ⊤ with hδtop | hδtop
      · exact ⟨0, fun n _ => by rw [hδtop]; exact le_top⟩
      · have hδr : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
        obtain ⟨N0, hN0⟩ := hcv δ.toReal hδr
        refine ⟨N0, fun N hN => ?_⟩
        change (⨆ n, ENNReal.ofReal |F N ω (dseq n) - G ω (dseq n)|) ≤ δ
        apply iSup_le
        intro n
        have hlt : |F N ω (dseq n) - G ω (dseq n)| < δ.toReal := hN0 N hN (dseq n) (dseq n).2
        have hle : ENNReal.ofReal |F N ω (dseq n) - G ω (dseq n)| ≤ ENNReal.ofReal δ.toReal :=
          ENNReal.ofReal_le_ofReal (le_of_lt hlt)
        rwa [ENNReal.ofReal_toReal hδtop] at hle
    let m : ℕ → Ω → ℝ := fun N ω => (min (M N ω) (ENNReal.ofReal (ε + 1))).toReal
    have hmmeas : ∀ N, Measurable (m N) := by
      intro N
      exact ENNReal.measurable_toReal.comp ((hMmeas N).min measurable_const)
    have hmtend : ∀ᵐ ω ∂μ, Tendsto (fun N => m N ω) atTop (𝓝 0) := by
      filter_upwards [hconv] with ω hcv
      rw [tendsto_order]
      constructor
      · intro a ha
        exact Filter.Eventually.of_forall (fun N => lt_of_lt_of_le ha ENNReal.toReal_nonneg)
      · intro b hb
        have hb2 : 0 < b / 2 := by linarith
        obtain ⟨N0, hN0⟩ := hcv (b / 2) hb2
        refine Filter.eventually_atTop.mpr ⟨N0, fun N hN => ?_⟩
        have hMle : M N ω ≤ ENNReal.ofReal (b / 2) := by
          change (⨆ n, ENNReal.ofReal |F N ω (dseq n) - G ω (dseq n)|) ≤ ENNReal.ofReal (b / 2)
          apply iSup_le
          intro n
          exact ENNReal.ofReal_le_ofReal (le_of_lt (hN0 N hN (dseq n) (dseq n).2))
        have hMcap_le : min (M N ω) (ENNReal.ofReal (ε + 1)) ≤ ENNReal.ofReal (b / 2) :=
          (min_le_left _ _).trans hMle
        have hlt : m N ω ≤ (ENNReal.ofReal (b / 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hMcap_le
        rw [ENNReal.toReal_ofReal hb2.le] at hlt
        linarith
    have hTIM : TendstoInMeasure μ m atTop (fun _ => (0 : ℝ)) :=
      tendstoInMeasure_of_tendsto_ae (fun N => (hmmeas N).aestronglyMeasurable) hmtend
    have hgood : ∀ᵐ ω ∂μ, (∀ N, ContinuousOn (F N ω) K) ∧ ContinuousOn (G ω) K := hcont.and hcontG
    have hgoodm : μ {ω | ¬ ((∀ N, ContinuousOn (F N ω) K) ∧ ContinuousOn (G ω) K)} = 0 :=
      ae_iff.mp hgood
    have hsubset : ∀ N, {ω : Ω | ∃ x ∈ K, ε ≤ |F N ω x - G ω x|} ⊆
        {ω : Ω | ε ≤ dist (m N ω) 0} ∪
          {ω : Ω | ¬ ((∀ N, ContinuousOn (F N ω) K) ∧ ContinuousOn (G ω) K)} := by
      intro N ω hω
      by_cases hg : (∀ N, ContinuousOn (F N ω) K) ∧ ContinuousOn (G ω) K
      · left
        change ε ≤ dist (m N ω) 0
        obtain ⟨x, hxK, hxε⟩ := hω
        have hFc : Continuous (fun y : ↥K => F N ω (y : SpatialCoordinates d)) := (hg.1 N).domRestrict
        have hGc : Continuous (fun y : ↥K => G ω (y : SpatialCoordinates d)) := hg.2.domRestrict
        have hcont : Continuous (fun y : ↥K =>
            ENNReal.ofReal |F N ω (y : SpatialCoordinates d) - G ω (y : SpatialCoordinates d)|) :=
          ENNReal.continuous_ofReal.comp (continuous_abs.comp (hFc.sub hGc))
        have hEclosed : IsClosed {y : ↥K |
            ENNReal.ofReal |F N ω (y : SpatialCoordinates d) - G ω (y : SpatialCoordinates d)| ≤ M N ω} :=
          (isClosed_Iic (a := M N ω)).preimage hcont
        have hEsub : Set.range dseq ⊆ {y : ↥K |
            ENNReal.ofReal |F N ω (y : SpatialCoordinates d) - G ω (y : SpatialCoordinates d)| ≤ M N ω} := by
          rintro y ⟨n, rfl⟩
          change ENNReal.ofReal |F N ω (dseq n) - G ω (dseq n)| ≤
            ⨆ k, ENNReal.ofReal |F N ω (dseq k) - G ω (dseq k)|
          exact le_iSup (fun k => ENNReal.ofReal |F N ω (dseq k) - G ω (dseq k)|) n
        have hcl := closure_minimal hEsub hEclosed
        rw [hdseq.closure_range] at hcl
        have hxS : ENNReal.ofReal |F N ω x - G ω x| ≤ M N ω :=
          hcl (Set.mem_univ (⟨x, hxK⟩ : ↥K))
        have hεM : ENNReal.ofReal ε ≤ M N ω :=
          (ENNReal.ofReal_le_ofReal hxε).trans hxS
        have hMcap_ge : ENNReal.ofReal ε ≤ min (M N ω) (ENNReal.ofReal (ε + 1)) :=
          le_min hεM (ENNReal.ofReal_le_ofReal (by linarith))
        have hcaptop : min (M N ω) (ENNReal.ofReal (ε + 1)) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
        have hεm : ε ≤ m N ω := by
          have h : (ENNReal.ofReal ε).toReal ≤ (min (M N ω) (ENNReal.ofReal (ε + 1))).toReal :=
            ENNReal.toReal_mono hcaptop hMcap_ge
          rw [ENNReal.toReal_ofReal hε.le] at h
          exact h
        have hmnn : 0 ≤ m N ω := ENNReal.toReal_nonneg
        rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg hmnn]
        exact hεm
      · right; exact hg
    have hdist := tendstoInMeasure_iff_dist.mp hTIM ε hε
    rw [ENNReal.tendsto_atTop_zero] at hdist
    obtain ⟨N0, hN0⟩ := hdist (ENNReal.ofReal rho) (ENNReal.ofReal_pos.mpr hrho)
    refine ⟨N0, fun N hN => ?_⟩
    calc μ {ω : Ω | ∃ x ∈ K, ε ≤ |F N ω x - G ω x|}
        ≤ μ ({ω : Ω | ε ≤ dist (m N ω) 0} ∪
              {ω : Ω | ¬ ((∀ N, ContinuousOn (F N ω) K) ∧ ContinuousOn (G ω) K)}) :=
            measure_mono (hsubset N)
      _ ≤ μ {ω : Ω | ε ≤ dist (m N ω) 0} +
            μ {ω : Ω | ¬ ((∀ N, ContinuousOn (F N ω) K) ∧ ContinuousOn (G ω) K)} :=
            measure_union_le _ _
      _ ≤ ENNReal.ofReal rho + 0 := add_le_add (hN0 N hN) (le_of_eq hgoodm)
      _ = ENNReal.ofReal rho := by rw [add_zero]
  · refine ⟨0, fun N _ => ?_⟩
    have hempty : {ω : Ω | ∃ x ∈ K, ε ≤ |F N ω x - G ω x|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      obtain ⟨x, hx, _⟩ := hω
      exact hKne ⟨x, hx⟩
    rw [hempty, measure_empty]
    exact bot_le

theorem aux_prop_uniform_resolvent_subsequence_bridge_full_limit_identification {d : ℕ} (K : Set (SpatialCoordinates d)) (U : Set (SpatialCoordinates d))
    (hKc : IsCompact K) (hUopen : IsOpen U) (_hUne : U.Nonempty) (hUcl : closure U = K)
    (u : ℕ → SpatialCoordinates d → ℝ) (w : SpatialCoordinates d → ℝ)
    (hcont : ∀ N, ContinuousOn (u N) K)
    (hzero : ∀ N, ∀ x ∈ frontier K, u N x = 0)
    (hbdd : ∃ B : ℝ, ∀ N, ∀ x ∈ K, |u N x| ≤ B)
    (C : ℝ) (hCnonneg : 0 ≤ C)
    (hC : ∀ N, ∀ x ∈ K, ∀ y ∈ K, |u N x - u N y| ≤ C * dist x y ^ (1 / 4 : ℝ))
    (hidentify : ∀ g : SpatialCoordinates d → ℝ, ContinuousOn g K →
        (∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
            ∀ x ∈ K, |u (σ k) x - g x| < eps) →
        g =ᵐ[volume.restrict U] w) :
    ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g K ∧ (∀ x ∈ frontier K, g x = 0) ∧
      (∀ x ∈ K, Filter.limsup (fun N => u N x) atTop = g x) ∧
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ x ∈ K, |u k x - g x| < eps) ∧
      (∀ x ∈ K, ∀ y ∈ K, |g x - g y| ≤ C * dist x y ^ (1 / 4 : ℝ)) ∧
      g =ᵐ[volume.restrict U] w := by
  classical
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨τ, hτ, g0, hg0cont, hg0unif⟩ :=
    aux_prop_uniform_resolvent_subsequence_bridge_subseq_uniform_extract K hKc u hcont ⟨B, hB⟩ ⟨C, hCnonneg, hC⟩ id strictMono_id
  have hg0eqw : g0 =ᵐ[volume.restrict U] w :=
    hidentify g0 hg0cont ⟨τ, hτ, hg0unif⟩
  have hfull : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ x ∈ K, |u k x - g0 x| < eps := by
    by_contra hcon
    push Not at hcon
    obtain ⟨eps, heps, hbad⟩ := hcon
    have hbad' : ∀ N : ℕ, ∃ n > N, ∃ x ∈ K, eps ≤ |u n x - g0 x| := by
      intro N
      obtain ⟨k, hk, hkP⟩ := hbad (N + 1)
      exact ⟨k, Nat.lt_of_succ_le hk, hkP⟩
    obtain ⟨σ, hσ, hσbad⟩ := Nat.exists_strictMono_subsequence hbad'
    obtain ⟨τ', hτ', h, hhcont, hhunif⟩ :=
      aux_prop_uniform_resolvent_subsequence_bridge_subseq_uniform_extract K hKc (fun k => u (σ k)) (fun k => hcont (σ k))
        ⟨B, fun k => hB (σ k)⟩ ⟨C, hCnonneg, fun k => hC (σ k)⟩ id strictMono_id
    have hhew : h =ᵐ[volume.restrict U] w :=
      hidentify h hhcont ⟨fun k => σ (τ' k), hσ.comp hτ', hhunif⟩
    have hheq_g0 : h =ᵐ[volume.restrict U] g0 := hhew.trans hg0eqw.symm
    have hUK : U ⊆ K := by intro x hx; rw [← hUcl]; exact subset_closure hx
    have hKU : K ⊆ closure U := by intro x hx; rw [hUcl]; exact hx
    have heqonU : EqOn h g0 U :=
      lane2_eqOn_of_ae_eq_of_continuousOn (S := U) (f := h) (g := g0) hUopen
        (hhcont.mono hUK) (hg0cont.mono hUK) hheq_g0
    have heqon : EqOn h g0 K := heqonU.of_subset_closure hhcont hg0cont hUK hKU
    obtain ⟨k0, hk0⟩ := hhunif eps heps
    obtain ⟨x, hxK, hxbad⟩ := hσbad (τ' k0)
    have hlt := hk0 k0 le_rfl x hxK
    change |u (σ (τ' k0)) x - h x| < eps at hlt
    rw [heqon hxK] at hlt
    exact absurd hlt (not_lt_of_ge hxbad)
  have hptwise : ∀ x ∈ K, Tendsto (fun k => u k x) atTop (𝓝 (g0 x)) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro eps heps
    obtain ⟨k0, hk0⟩ := hfull eps heps
    exact ⟨k0, fun k hk => by
      rw [Real.dist_eq]
      exact hk0 k hk x hx⟩
  have hfront : ∀ x ∈ frontier K, g0 x = 0 := by
    intro x hx
    have hxK : x ∈ K := by
      have hfx := frontier_subset_closure hx
      rwa [hKc.isClosed.closure_eq] at hfx
    have hone : |g0 x| = 0 := by
      by_contra hne
      have hpos : 0 < |g0 x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      obtain ⟨k0, hk0⟩ := hg0unif |g0 x| hpos
      have hlt := hk0 k0 le_rfl x hxK
      have hz : u (id (τ k0)) x = 0 := hzero (τ k0) x hx
      rw [hz, zero_sub, abs_neg] at hlt
      exact absurd hlt (lt_irrefl _)
    exact abs_eq_zero.mp hone
  have hlimsup : ∀ x ∈ K, Filter.limsup (fun N => u N x) atTop = g0 x := by
    intro x hx
    exact (hptwise x hx).limsup_eq
  have hholder : ∀ x ∈ K, ∀ y ∈ K, |g0 x - g0 y| ≤ C * dist x y ^ (1 / 4 : ℝ) := by
    intro x hx y hy
    have htend : Tendsto (fun k => |u k x - u k y|) atTop (𝓝 |g0 x - g0 y|) :=
      ((hptwise x hx).sub (hptwise y hy)).abs
    exact le_of_tendsto' htend (fun k => hC k x hx y hy)
  exact ⟨g0, hg0cont, hfront, hlimsup, hfull, hholder, hg0eqw⟩



theorem aux_prop_uniform_resolvent_subsequence_bridge_holder_continuousOn
    {X : Type*} [PseudoMetricSpace X] (g : X → ℝ) (K : Set X) (C : ℝ)
    (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ y ∈ K,
      |g x - g y| ≤ C * dist x y ^ (1 / 4 : ℝ)) : ContinuousOn g K := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hden : (0 : ℝ) < 2 * (C + 1) := by linarith
  have hpos : 0 < ε / (2 * (C + 1)) := div_pos hε hden
  refine ⟨(ε / (2 * (C + 1))) ^ (4 : ℝ),
    Real.rpow_pos_of_pos hpos 4, fun y hy hxy => ?_⟩
  have h4 : ((ε / (2 * (C + 1))) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) =
      ε / (2 * (C + 1)) := by
    rw [← Real.rpow_mul hpos.le]
    norm_num
  have hlt : dist y x ^ (1 / 4 : ℝ) < ε / (2 * (C + 1)) := by
    have h1 := Real.rpow_lt_rpow dist_nonneg hxy (by norm_num : (0 : ℝ) < 1 / 4)
    rwa [h4] at h1
  have hstep : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
    have h1 : C * (ε / (2 * (C + 1))) ≤
        (C + 1) * (ε / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    have h2 : (C + 1) * (ε / (2 * (C + 1))) = ε / 2 := by
      field_simp
    linarith
  rw [Real.dist_eq]
  calc
    |g y - g x| = |g x - g y| := abs_sub_comm _ _
    _ ≤ C * dist x y ^ (1 / 4 : ℝ) := h x hx y hy
    _ = C * dist y x ^ (1 / 4 : ℝ) := by rw [dist_comm]
    _ ≤ C * (ε / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hlt.le hC
    _ ≤ ε / 2 := hstep
    _ < ε := by linarith



theorem prop_uniform_resolvent_subsequence_bridge
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (RN : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (ustar : BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hRNmeas : ∀ N : ℕ, ∀ lam : ℝ,
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x : SpatialCoordinates d, Measurable (fun omega => RN N omega lam f x))
    (hcutoff : ∀ᵐ omega ∂P, ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (RN N omega lam f)
          (closure ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
          RN N omega lam f x = 0) ∧
        (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
          ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            |RN N omega lam f x - RN N omega lam f y| ≤
              C * ‖f‖ * dist x y ^ (1 / 4 : ℝ)))
    (hidentify : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ g : C(SpatialCoordinates d, ℝ),
        (∃ σ : ℕ → ℕ, StrictMono σ ∧
            ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
              ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |RN (σ k) omega lam f x - g x| < eps) →
        ((g : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
          (ustar omega lam f : SpatialCoordinates d → ℝ))) :
    ∃ R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        BilateralField d → C(SpatialCoordinates d, ℝ),
      (∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ σ : ℕ → ℕ, StrictMono σ →
          ∃ τ : ℕ → ℕ, StrictMono τ ∧
            ∃ g : C(SpatialCoordinates d, ℝ),
              (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
                ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                  |RN (σ (τ k)) omega lam f x - g x| < eps) ∧
              ((g : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
                (ustar omega lam f : SpatialCoordinates d → ℝ))) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Measurable (R lam f)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            P {omega : BilateralField d |
                ∃ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                  eps ≤ |RN N omega lam f x - R lam f omega x|} ≤
              ENNReal.ofReal rho) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P,
          ∃ CH : ℝ, 0 < CH ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |R lam f omega x - R lam f omega y| ≤
                  CH * ‖f‖ * dist x y ^ (1 / 4 : ℝ))) := by
  classical
  set Uo : Set (SpatialCoordinates d) := (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) with hUo
  set U : Set (SpatialCoordinates d) := closure Uo with hU
  have hKc : IsCompact U := by rw [hU]; exact (centeredCube_isBounded (Homogenization.cubeCenter Qtri) hr).isCompact_closure
  have hUopen : IsOpen Uo := by rw [hUo]; exact (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr).isOpen
  have hUcl : closure Uo = U := hU.symm
  have hUne : Uo.Nonempty := by
    refine ⟨Homogenization.cubeCenter Qtri, ?_⟩
    rw [hUo, centeredCube_eq_pi (Homogenization.cubeCenter Qtri) hr, Set.mem_pi]
    intro i _
    rw [Set.mem_Ioo]
    exact ⟨by linarith [hr], by linarith [hr]⟩
  let p1 : BilateralField d → Prop := fun omega => ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (RN N omega lam f) U ∧
        (∀ x ∈ frontier Uo, RN N omega lam f x = 0) ∧
        ∀ x ∈ U, ∀ y ∈ U,
          |RN N omega lam f x - RN N omega lam f y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ)
  let p2 : BilateralField d → Prop := fun omega =>
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ g : C(SpatialCoordinates d, ℝ),
        (∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
            ∀ x ∈ U, |RN (σ k) omega lam f x - g x| < eps) →
        ((g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Uo] (ustar omega lam f : SpatialCoordinates d → ℝ))
  have hboth : ∀ᵐ omega ∂P, p1 omega ∧ p2 omega := by
    filter_upwards [hcutoff, hidentify] with omega h1 h2
    exact ⟨by simpa [p1, p2, U, Uo] using h1, by simpa [p1, p2, U, Uo] using h2⟩
  set bad : Set (BilateralField d) := toMeasurable P {omega : BilateralField d | ¬ (p1 omega ∧ p2 omega)} with hbad
  set good : Set (BilateralField d) := badᶜ with hgood
  have hgoodmeas : MeasurableSet good := by
    rw [hgood]; exact (measurableSet_toMeasurable P _).compl
  have hgoodzero : P goodᶜ = 0 := by
    rw [hgood, compl_compl, hbad, measure_toMeasurable]
    exact MeasureTheory.ae_iff.mp hboth
  have hgoodsub : ∀ omega ∈ good, p1 omega ∧ p2 omega := by
    intro omega homega
    have h1 : omega ∉ toMeasurable P {omega : BilateralField d | ¬ (p1 omega ∧ p2 omega)} := by
      rw [hgood, hbad] at homega; exact homega
    by_contra hcon
    exact h1 (subset_toMeasurable P _ hcon)
  have hmain : ∀ (omega : BilateralField d), omega ∈ good → ∀ (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g U ∧
        (∀ x ∈ frontier U, g x = 0) ∧
        (∀ x ∈ U, Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop = g x) ∧
        (∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ x ∈ U,
            |RN N omega lam f x - g x| < eps) ∧
        (g =ᵐ[volume.restrict Uo] (ustar omega lam f : SpatialCoordinates d → ℝ)) := by
    intro omega homega lam hlam f
    obtain ⟨hp1v, hp2v⟩ := hgoodsub omega homega
    obtain ⟨C, hCpos, hCbd⟩ := hp1v
    have hcont : ∀ N, ContinuousOn (RN N omega lam f) U := fun N => (hCbd N lam hlam f).1
    have hzero : ∀ N, ∀ x ∈ frontier U, RN N omega lam f x = 0 := by
      intro N x hx
      apply (hCbd N lam hlam f).2.1 x
      simpa [U] using (frontier_closure_subset (s := Uo) hx)
    have hholder : ∀ N, ∀ x ∈ U, ∀ y ∈ U,
        |RN N omega lam f x - RN N omega lam f y| ≤ C * ‖f‖ * dist x y ^ (1/4:ℝ) := fun N => (hCbd N lam hlam f).2.2
    have hbdd : ∃ B : ℝ, ∀ N, ∀ x ∈ U, |RN N omega lam f x| ≤ B := by
      obtain ⟨D, hD0, hDnear⟩ := aux_prop_uniform_resolvent_subsequence_bridge_cube_frontier_near hd Qtri hr
      refine ⟨C * ‖f‖ * D ^ (1/4:ℝ), fun N x hx => ?_⟩
      obtain ⟨y, hy, hdist⟩ := hDnear x hx
      have hyU : y ∈ U := by simpa [U] using (frontier_subset_closure hy)
      calc |RN N omega lam f x| = |RN N omega lam f x - RN N omega lam f y| := by rw [hzero N y hy, sub_zero]
        _ ≤ C * ‖f‖ * dist x y ^ (1/4:ℝ) := hholder N x hx y hyU
        _ ≤ C * ‖f‖ * D ^ (1/4:ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCpos.le (norm_nonneg f))
            exact Real.rpow_le_rpow dist_nonneg hdist (by norm_num)
    have hident : ∀ g : SpatialCoordinates d → ℝ, ContinuousOn g U →
        (∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
            ∀ x ∈ U, |RN (σ k) omega lam f x - g x| < eps) →
        g =ᵐ[volume.restrict Uo] (ustar omega lam f : SpatialCoordinates d → ℝ) := by
      intro g hgc hex
      obtain ⟨σ, hσ, hconv⟩ := hex
      have hgz : ∀ x ∈ frontier U, g x = 0 := by
        intro x hx
        have hxU : x ∈ U := hKc.isClosed.closure_eq ▸ frontier_subset_closure hx
        have h0 : ∀ k, RN (σ k) omega lam f x = 0 := fun k => hzero (σ k) x hx
        have hle : |g x| ≤ 0 := le_of_forall_pos_lt_add (fun e he => by
          obtain ⟨k0, hk0⟩ := hconv e he
          have hk := hk0 k0 le_rfl x hxU
          rw [h0 k0] at hk
          simp only [zero_sub, abs_neg] at hk
          linarith)
        exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
      have hgcont' : Continuous (fun x : SpatialCoordinates d => if x ∈ U then g x else 0) :=
        aux_prop_uniform_resolvent_subsequence_bridge_zero_extend_continuous U g hKc.isClosed hgc hgz
      set g' : C(SpatialCoordinates d, ℝ) := ⟨fun x => if x ∈ U then g x else 0, hgcont'⟩ with hg'def
      have hg'eq : ∀ x ∈ U, g' x = g x := by
        intro x hx; rw [hg'def]; simp only [ContinuousMap.coe_mk, ite_eq_left hx]
      have hgp : g' =ᵐ[volume.restrict Uo] (ustar omega lam f : SpatialCoordinates d → ℝ) :=
        hp2v lam hlam f g' ⟨σ, hσ, fun eps heps => by
          obtain ⟨k0, hk0⟩ := hconv eps heps
          exact ⟨k0, fun k hk x hx => by
            simpa only [hg'eq x hx] using hk0 k hk x hx⟩⟩
      have hUsub : Uo ⊆ U := by rw [← hUcl]; exact subset_closure
      have h1 : g =ᵐ[volume.restrict Uo] g' := by
        show ∀ᵐ x ∂(volume.restrict Uo), g x = g' x
        rw [MeasureTheory.ae_restrict_iff' hUopen.measurableSet]
        exact Filter.Eventually.of_forall (fun x hx => (hg'eq x (hUsub hx)).symm)
      exact h1.trans hgp
    obtain ⟨g, hgcont, hgfront, hglim, hgfull, hghold, hgeq⟩ :=
      aux_prop_uniform_resolvent_subsequence_bridge_full_limit_identification U Uo hKc hUopen hUne hUcl (fun N => RN N omega lam f)
        (ustar omega lam f : SpatialCoordinates d → ℝ) hcont hzero hbdd (C * ‖f‖)
        (mul_nonneg hCpos.le (norm_nonneg f)) hholder hident
    exact ⟨g, hgcont, hgfront, hglim, hgfull, hgeq⟩
  let Gfun : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun lam f omega x => if omega ∈ good ∧ 0 < lam then
      (if x ∈ U then Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop else 0) else 0
  have hGfun_cont : ∀ (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
      (omega : BilateralField d), omega ∈ good → 0 < lam → Continuous (Gfun lam f omega) := by
    intro lam f omega homega hlam
    have heq : Gfun lam f omega = fun x : SpatialCoordinates d =>
        if x ∈ U then Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop else 0 := by
      funext x; dsimp only [Gfun]; rw [ite_eq_left ⟨homega, hlam⟩]
    rw [heq]
    obtain ⟨g, hgcont, hgfront, hglim, hgfull, hgeq⟩ := hmain omega homega lam hlam f
    have heq2 : (fun x : SpatialCoordinates d =>
        if x ∈ U then Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop else 0)
        = fun x => if x ∈ U then g x else 0 := by
      funext x
      by_cases hx : x ∈ U
      · rw [ite_eq_left hx, ite_eq_left hx, hglim x hx]
      · rw [ite_eq_right hx, ite_eq_right hx]
    rw [heq2]
    exact aux_prop_uniform_resolvent_subsequence_bridge_zero_extend_continuous U g hKc.isClosed hgcont hgfront
  let R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun lam f omega => ⟨Gfun lam f omega, by
      by_cases h : omega ∈ good ∧ 0 < lam
      · exact hGfun_cont lam f omega h.1 h.2
      · have heq : Gfun lam f omega = fun _ : SpatialCoordinates d => (0:ℝ) := by
          funext x; dsimp only [Gfun]; rw [ite_eq_right h]
        rw [heq]; exact continuous_const⟩
  have hevalR : ∀ (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
      (x : SpatialCoordinates d), Measurable (fun omega => R lam f omega x) := by
    intro lam f x
    have h1 : (fun omega => R lam f omega x) = fun omega =>
        if omega ∈ good ∧ 0 < lam then
          (if x ∈ U then Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop else 0) else 0 := by
      funext omega; rfl
    rw [h1]
    by_cases hlam : 0 < lam
    · have h2 : (fun omega : BilateralField d =>
          if omega ∈ good ∧ 0 < lam then
            (if x ∈ U then Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop else 0) else 0)
          = fun omega => if omega ∈ good then
            (if x ∈ U then Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop else 0) else 0 := by
        funext omega
        by_cases hg : omega ∈ good
        · rw [ite_eq_left ⟨hg, hlam⟩, ite_eq_left hg]
        · rw [ite_eq_right (fun h => hg h.1), ite_eq_right hg]
      rw [h2]
      refine Measurable.ite hgoodmeas ?_ measurable_const
      by_cases hx : x ∈ U
      · rw [show (fun omega => (if x ∈ U then Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop else 0))
            = (fun omega => Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop) from by funext omega; rw [ite_eq_left hx]]
        exact Measurable.limsup (fun N => hRNmeas N lam f x)
      · rw [show (fun omega => (if x ∈ U then Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop else 0))
            = (fun _ => (0:ℝ)) from by funext omega; rw [ite_eq_right hx]]
        exact measurable_const
    · rw [show (fun omega : BilateralField d =>
          if omega ∈ good ∧ 0 < lam then
            (if x ∈ U then Filter.limsup (fun N : ℕ => RN N omega lam f x) atTop else 0) else 0)
          = (fun _ => (0:ℝ)) from by
            funext omega; rw [ite_eq_right (fun h => hlam h.2)]]
      exact measurable_const
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hcutoff, hidentify] with omega hcut hident
    intro lam hlam f σ hσ
    obtain ⟨C, hCpos, hCbd⟩ := hcut
    have hcont : ∀ N, ContinuousOn (RN N omega lam f) U := fun N => (hCbd N lam hlam f).1
    have hzero : ∀ N, ∀ x ∈ frontier U, RN N omega lam f x = 0 := by
      intro N x hx
      apply (hCbd N lam hlam f).2.1 x
      simpa [U] using (frontier_closure_subset (s := Uo) hx)
    have hholder : ∀ N, ∀ x ∈ U, ∀ y ∈ U,
        |RN N omega lam f x - RN N omega lam f y| ≤ C * ‖f‖ * dist x y ^ (1/4:ℝ) := fun N => (hCbd N lam hlam f).2.2
    have hbdd : ∃ B : ℝ, ∀ N, ∀ x ∈ U, |RN N omega lam f x| ≤ B := by
      obtain ⟨D, hD0, hDnear⟩ := aux_prop_uniform_resolvent_subsequence_bridge_cube_frontier_near hd Qtri hr
      refine ⟨C * ‖f‖ * D ^ (1/4:ℝ), fun N x hx => ?_⟩
      obtain ⟨y, hy, hdist⟩ := hDnear x hx
      have hyU : y ∈ U := by simpa [U] using (frontier_subset_closure hy)
      calc |RN N omega lam f x| = |RN N omega lam f x - RN N omega lam f y| := by rw [hzero N y hy, sub_zero]
        _ ≤ C * ‖f‖ * dist x y ^ (1/4:ℝ) := hholder N x hx y hyU
        _ ≤ C * ‖f‖ * D ^ (1/4:ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCpos.le (norm_nonneg f))
            exact Real.rpow_le_rpow dist_nonneg hdist (by norm_num)
    obtain ⟨τ, hτ, g, hgcont, hgconv⟩ := aux_prop_uniform_resolvent_subsequence_bridge_subseq_uniform_extract U hKc
      (fun N => RN N omega lam f) hcont hbdd ⟨C * ‖f‖, mul_nonneg hCpos.le (norm_nonneg f), hholder⟩ σ hσ
    have hgfront : ∀ x ∈ frontier U, g x = 0 := by
      intro x hx
      have hxU : x ∈ U := hKc.isClosed.closure_eq ▸ frontier_subset_closure hx
      have h0 : ∀ k, RN (σ (τ k)) omega lam f x = 0 := fun k => hzero (σ (τ k)) x hx
      have hle : |g x| ≤ 0 := le_of_forall_pos_lt_add (fun e he => by
        obtain ⟨k0, hk0⟩ := hgconv e he
        have hk := hk0 k0 le_rfl x hxU
        rw [h0 k0] at hk
        simp only [zero_sub, abs_neg] at hk
        linarith)
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    have hg'cont : Continuous (fun x : SpatialCoordinates d => if x ∈ U then g x else 0) :=
      aux_prop_uniform_resolvent_subsequence_bridge_zero_extend_continuous U g hKc.isClosed hgcont hgfront
    let g' : C(SpatialCoordinates d, ℝ) := ⟨fun x => if x ∈ U then g x else 0, hg'cont⟩
    have hg'eq : ∀ x ∈ U, g' x = g x := by
      intro x hx; simp only [g', ContinuousMap.coe_mk, ite_eq_left hx]
    refine ⟨τ, hτ, g', ?_, ?_⟩
    · intro eps heps
      obtain ⟨k0, hk0⟩ := hgconv eps heps
      exact ⟨k0, fun k hk x hx => by
        have hk2 := hk0 k hk x hx
        simpa only [hg'eq x hx, Function.comp_apply] using! hk2⟩
    · exact hident lam hlam f g' ⟨σ ∘ τ, hσ.comp hτ, fun eps heps => by
        obtain ⟨k0, hk0⟩ := hgconv eps heps
        exact ⟨k0, fun k hk x hx => by
          have hk2 := hk0 k hk x hx
          simpa only [hg'eq x hx, Function.comp_apply] using! hk2⟩⟩
  · intro lam hlam f
    exact aux_prop_uniform_resolvent_subsequence_bridge_measurable_contmap_of_eval
      (R lam f) (hevalR lam f)
  · intro lam hlam f eps heps rho hrho
    have hgood_ae : ∀ᵐ omega ∂P, omega ∈ good := by
      rw [MeasureTheory.ae_iff]
      simpa using! hgoodzero
    have hcont : ∀ᵐ omega ∂P, ∀ N, ContinuousOn (fun x : SpatialCoordinates d => RN N omega lam f x) U := by
      filter_upwards [hcutoff] with omega hcut
      obtain ⟨C, hCpos, hCbd⟩ := hcut
      intro N
      exact (hCbd N lam hlam f).1
    have hcontG : ∀ᵐ omega ∂P, ContinuousOn (fun x : SpatialCoordinates d => R lam f omega x) U := by
      filter_upwards [hgood_ae] with omega homega
      have hc : Continuous (Gfun lam f omega) := hGfun_cont lam f omega homega hlam
      have heq : (fun x : SpatialCoordinates d => R lam f omega x) = Gfun lam f omega := by
        funext x; rfl
      rw [heq]
      exact hc.continuousOn
    have hconv : ∀ᵐ omega ∂P, ∀ eps' : ℝ, 0 < eps' → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ x ∈ U, |RN N omega lam f x - R lam f omega x| < eps' := by
      filter_upwards [hgood_ae] with omega homega
      obtain ⟨g, hgcont, hgfront, hglim, hgfull, hgeq⟩ := hmain omega homega lam hlam f
      intro eps' heps'
      obtain ⟨N0, hN0⟩ := hgfull eps' heps'
      refine ⟨N0, fun N hN x hx => ?_⟩
      have hR : R lam f omega x = g x := by
        change Gfun lam f omega x = g x
        dsimp only [Gfun]
        rw [ite_eq_left ⟨homega, hlam⟩, ite_eq_left hx, hglim x hx]
      rw [hR]
      exact hN0 N hN x hx
    exact aux_prop_uniform_resolvent_subsequence_bridge_prob_bound_from_ae P U hKc (fun N omega => RN N omega lam f)
      (fun omega x => R lam f omega x) (fun N x => hRNmeas N lam f x) (fun x => hevalR lam f x)
      hcont hcontG hconv eps heps rho hrho
  · intro lam hlam f
    filter_upwards [hcutoff] with omega hcut
    obtain ⟨C, hCpos, hCbd⟩ := hcut
    refine ⟨C, hCpos, ?_⟩
    intro x hx y hy
    by_cases homega : omega ∈ good
    · obtain ⟨g, hgcont, hgfront, hglim, hgfull, hgeq⟩ := hmain omega homega lam hlam f
      have hRx : R lam f omega x = g x := by
        change Gfun lam f omega x = g x
        dsimp only [Gfun]; rw [ite_eq_left ⟨homega, hlam⟩, ite_eq_left hx, hglim x hx]
      have hRy : R lam f omega y = g y := by
        change Gfun lam f omega y = g y
        dsimp only [Gfun]; rw [ite_eq_left ⟨homega, hlam⟩, ite_eq_left hy, hglim y hy]
      rw [hRx, hRy]
      have htendx : Tendsto (fun N : ℕ => RN N omega lam f x) atTop (𝓝 (g x)) := by
        rw [Metric.tendsto_atTop]
        intro e he
        obtain ⟨N0, hN0⟩ := hgfull e he
        exact ⟨N0, fun N hN => by rw [Real.dist_eq]; exact hN0 N hN x hx⟩
      have htendy : Tendsto (fun N : ℕ => RN N omega lam f y) atTop (𝓝 (g y)) := by
        rw [Metric.tendsto_atTop]
        intro e he
        obtain ⟨N0, hN0⟩ := hgfull e he
        exact ⟨N0, fun N hN => by rw [Real.dist_eq]; exact hN0 N hN y hy⟩
      exact le_of_tendsto' ((htendx.sub htendy).abs) (fun N => (hCbd N lam hlam f).2.2 x hx y hy)
    · have hR0 : R lam f omega = 0 := by
        ext x
        change Gfun lam f omega x = 0
        dsimp only [Gfun]
        rw [ite_eq_right (fun h => homega h.1)]
      rw [hR0]
      simp only [ContinuousMap.zero_apply, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hCpos.le (norm_nonneg f)) (Real.rpow_nonneg dist_nonneg _)

end SubdiffusiveProcess.Paper
