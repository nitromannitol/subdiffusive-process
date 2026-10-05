module

public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Geometry.OddGridPartition
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.VariationalResponses.CellAssembly
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.lem_finite_stopping_moments

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Crude costs in the finite stopping partition

The proof controls the Dirichlet energy of the root and the final observation cells. It combines the large-root estimate `SubdiffusiveProcess.Paper.prop_growth_large_root` with the small-root estimate `SubdiffusiveProcess.Paper.prop_growth`, using the finite-stopping moment bounds. -/

open MeasureTheory Set TopologicalSpace Filter
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped NNReal ENNReal ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper


variable {d : ℕ}

/-- The length-`k` prefix of a word of length `n`. -/
def aux_lem_finite_stopping_crude_cost_wordPrefix {α : Type*} {n : ℕ} (w : Fin n → α) (k : ℕ) (hk : k ≤ n) : Fin k → α :=
  fun i => w (Fin.castLE hk i)

theorem aux_lem_finite_stopping_crude_cost_wordPrefix_self {α : Type*} {n : ℕ} (w : Fin n → α) (hk : n ≤ n) :
    aux_lem_finite_stopping_crude_cost_wordPrefix w n hk = w := by
  funext i
  simp [aux_lem_finite_stopping_crude_cost_wordPrefix]

theorem aux_lem_finite_stopping_crude_cost_wordPrefix_wordPrefix {α : Type*} {n : ℕ} (w : Fin n → α) (k l : ℕ)
    (hk : k ≤ n) (hl : l ≤ k) :
    aux_lem_finite_stopping_crude_cost_wordPrefix (aux_lem_finite_stopping_crude_cost_wordPrefix w k hk) l hl = aux_lem_finite_stopping_crude_cost_wordPrefix w l (hl.trans hk) := by
  funext i
  rfl

theorem aux_lem_finite_stopping_crude_cost_wordPrefix_castSucc {α : Type*} {n : ℕ} (w : Fin (n + 1) → α) (k : ℕ)
    (hk : k ≤ n) :
    aux_lem_finite_stopping_crude_cost_wordPrefix (fun i : Fin n => w i.castSucc) k hk =
      aux_lem_finite_stopping_crude_cost_wordPrefix w k (hk.trans (Nat.le_succ n)) := by
  funext i
  rfl

/-- The one-step identity: a depth-`n+1` cell is the odd-grid child of its parent cell. -/
theorem aux_lem_finite_stopping_crude_cost_descendantCell_succ_eq_oddGridCell (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (n : ℕ) (w : Fin (n + 1) → OddGridIndex d m) :
    (descendantCell m z hr (n + 1) w : Set (SpatialCoordinates d)) =
      oddGridCell (descendantCenter m z r n fun i => w i.castSucc)
        (descendantSide m n r) (descendantSide_pos m n hr) m (w (Fin.last n)) := by
  rw [descendantCell_coe, oddGridCell_coe, descendantSide_succ]
  rfl

theorem aux_lem_finite_stopping_crude_cost_descendantCell_zero (m : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (w : Fin 0 → OddGridIndex d m) :
    (descendantCell m z hr 0 w : Set (SpatialCoordinates d)) = centeredCube z r hr := by
  rw [descendantCell_coe]
  change Metric.ball z (descendantSide m 0 r / 2) = Metric.ball z (r / 2)
  rw [descendantSide_zero]

/-- A cell lies in the cell of each of its prefixes. -/
theorem aux_lem_finite_stopping_crude_cost_descendantCell_subset_prefix (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    ∀ (n : ℕ) (w : Fin n → OddGridIndex d m) (k : ℕ) (hk : k ≤ n),
      (descendantCell m z hr n w : Set (SpatialCoordinates d)) ⊆
        descendantCell m z hr k (aux_lem_finite_stopping_crude_cost_wordPrefix w k hk) := by
  intro n
  induction n with
  | zero =>
    intro w k hk
    obtain rfl : k = 0 := by omega
    rw [aux_lem_finite_stopping_crude_cost_descendantCell_zero, aux_lem_finite_stopping_crude_cost_descendantCell_zero]
  | succ n ih =>
    intro w k hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hkn : k ≤ n := by omega
      refine (descendantCell_succ_subset m z hr n w).trans ?_
      have h := ih (fun i => w i.castSucc) k hkn
      rwa [aux_lem_finite_stopping_crude_cost_wordPrefix_castSucc] at h
    · obtain rfl : k = n + 1 := by omega
      rw [aux_lem_finite_stopping_crude_cost_wordPrefix_self]

/-- Every descendant cell lies in the root cube. -/
theorem aux_lem_finite_stopping_crude_cost_descendantCell_subset_root (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (n : ℕ) (w : Fin n → OddGridIndex d m) :
    (descendantCell m z hr n w : Set (SpatialCoordinates d)) ⊆ centeredCube z r hr := by
  have h := aux_lem_finite_stopping_crude_cost_descendantCell_subset_prefix m z hr n w 0 (Nat.zero_le n)
  rwa [aux_lem_finite_stopping_crude_cost_descendantCell_zero] at h

/-- Two cells of the same depth that share a point carry the same word. -/
theorem aux_lem_finite_stopping_crude_cost_descendantCell_word_eq_of_mem (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    ∀ (n : ℕ) (w w' : Fin n → OddGridIndex d m) (x : SpatialCoordinates d),
      x ∈ (descendantCell m z hr n w : Set (SpatialCoordinates d)) →
      x ∈ (descendantCell m z hr n w' : Set (SpatialCoordinates d)) → w = w' := by
  intro n
  induction n with
  | zero =>
    intro w w' _ _ _
    funext i
    exact i.elim0
  | succ n ih =>
    intro w w' x hx hx'
    have hinit : (fun i : Fin n => w i.castSucc) = fun i => w' i.castSucc :=
      ih _ _ x (descendantCell_succ_subset m z hr n w hx)
        (descendantCell_succ_subset m z hr n w' hx')
    have hlast : w (Fin.last n) = w' (Fin.last n) := by
      by_contra hne
      rw [aux_lem_finite_stopping_crude_cost_descendantCell_succ_eq_oddGridCell] at hx hx'
      rw [hinit] at hx
      exact (oddGridCell_pairwiseDisjoint _ (descendantSide_pos m n hr) m hne).le_bot
        ⟨hx, hx'⟩
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact congrFun hinit j
    · exact hlast

/-- The depth-`n` cells cover the root cube up to a null set. -/
theorem aux_lem_finite_stopping_crude_cost_descendantCells_union_ae_eq (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    ∀ n : ℕ, (⋃ w : Fin n → OddGridIndex d m,
      (descendantCell m z hr n w : Set (SpatialCoordinates d))) =ᵐ[volume]
        (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  intro n
  induction n with
  | zero =>
    have h : (⋃ w : Fin 0 → OddGridIndex d m,
        (descendantCell m z hr 0 w : Set (SpatialCoordinates d))) =
          centeredCube z r hr := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun w => (aux_lem_finite_stopping_crude_cost_descendantCell_zero m z hr w).le
      · intro x hx
        exact Set.mem_iUnion.2 ⟨Fin.elim0, by rw [aux_lem_finite_stopping_crude_cost_descendantCell_zero]; exact hx⟩
    rw [h]
  | succ n ih =>
    have hset : (⋃ w : Fin (n + 1) → OddGridIndex d m,
        (descendantCell m z hr (n + 1) w : Set (SpatialCoordinates d))) =
        ⋃ v : Fin n → OddGridIndex d m, ⋃ l : OddGridIndex d m,
          (oddGridCell (descendantCenter m z r n v) (descendantSide m n r)
            (descendantSide_pos m n hr) m l : Set (SpatialCoordinates d)) := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨w, hw⟩
        rw [aux_lem_finite_stopping_crude_cost_descendantCell_succ_eq_oddGridCell] at hw
        exact ⟨_, _, hw⟩
      · rintro ⟨v, l, hvl⟩
        refine ⟨Fin.snoc (α := fun _ => OddGridIndex d m) v l, ?_⟩
        rw [aux_lem_finite_stopping_crude_cost_descendantCell_succ_eq_oddGridCell]
        have hv : (fun i : Fin n =>
            (Fin.snoc (α := fun _ => OddGridIndex d m) v l) i.castSucc) = v := by
          funext i
          simp
        rw [hv, Fin.snoc_last]
        exact hvl
    rw [hset]
    refine (EventuallyEqSet.countable_iUnion fun v => ?_).trans ih
    exact oddGrid_union_ae_eq (descendantCenter m z r n v) (descendantSide_pos m n hr) m

/-! ## Stopping leaves -/

/-- A leaf of the stopping tree: stopped or at the final depth, with no stopped
proper prefix. -/
def aux_lem_finite_stopping_crude_cost_IsLeaf {m : ℕ} (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax n : ℕ)
    (w : Fin n → OddGridIndex d m) : Prop :=
  n ≤ nmax ∧ (stop n w ∨ n = nmax) ∧
    ∀ (k : ℕ) (hk : k < n), ¬ stop k (aux_lem_finite_stopping_crude_cost_wordPrefix w k hk.le)

/-- Distinct leaves have disjoint cells. -/
theorem aux_lem_finite_stopping_crude_cost_leaf_cells_disjoint {m : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax : ℕ)
    {n n' : ℕ} {w : Fin n → OddGridIndex d m} {w' : Fin n' → OddGridIndex d m}
    (hw : aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax n w) (hw' : aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax n' w')
    (hne : (⟨n, w⟩ : Σ k, Fin k → OddGridIndex d m) ≠ ⟨n', w'⟩) :
    Disjoint (descendantCell m z hr n w : Set (SpatialCoordinates d))
      (descendantCell m z hr n' w' : Set (SpatialCoordinates d)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  -- the two words are comparable; the shorter is a prefix of the longer
  have key : ∀ {a b : ℕ} {u : Fin a → OddGridIndex d m} {v : Fin b → OddGridIndex d m},
      aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax a u → aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax b v →
      x ∈ (descendantCell m z hr a u : Set (SpatialCoordinates d)) →
      x ∈ (descendantCell m z hr b v : Set (SpatialCoordinates d)) → a < b → False := by
    intro a b u v hu hv hxu hxv hab
    have hxv' := aux_lem_finite_stopping_crude_cost_descendantCell_subset_prefix m z hr b v a hab.le hxv
    have hpre : u = aux_lem_finite_stopping_crude_cost_wordPrefix v a hab.le :=
      aux_lem_finite_stopping_crude_cost_descendantCell_word_eq_of_mem m z hr a u _ x hxu hxv'
    rcases hu.2.1 with hstop | hmax
    · exact hv.2.2 a hab (hpre ▸ hstop)
    · have := hv.1
      omega
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · exact key hw hw' hx hx' hlt
  · subst heq
    exact hne (by rw [aux_lem_finite_stopping_crude_cost_descendantCell_word_eq_of_mem m z hr n w w' x hx hx'])
  · exact key hw' hw hx' hx hgt

/-- Every point of a depth-`nmax` cell lies in a leaf cell. -/
theorem aux_lem_finite_stopping_crude_cost_exists_leaf_of_mem {m : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax : ℕ)
    (w : Fin nmax → OddGridIndex d m) (x : SpatialCoordinates d)
    (hx : x ∈ (descendantCell m z hr nmax w : Set (SpatialCoordinates d))) :
    ∃ (n : ℕ) (v : Fin n → OddGridIndex d m), aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax n v ∧
      x ∈ (descendantCell m z hr n v : Set (SpatialCoordinates d)) := by
  classical
  let P : ℕ → Prop := fun k => ∃ hk : k ≤ nmax, stop k (aux_lem_finite_stopping_crude_cost_wordPrefix w k hk) ∨ k = nmax
  have hP : ∃ k, P k := ⟨nmax, le_rfl, Or.inr rfl⟩
  let k := Nat.find hP
  obtain ⟨hk, hstop⟩ : P k := Nat.find_spec hP
  refine ⟨k, aux_lem_finite_stopping_crude_cost_wordPrefix w k hk, ⟨hk, hstop, ?_⟩, ?_⟩
  · intro l hl hsl
    have hmin := Nat.find_min hP hl
    apply hmin
    refine ⟨hl.le.trans hk, Or.inl ?_⟩
    rwa [aux_lem_finite_stopping_crude_cost_wordPrefix_wordPrefix] at hsl
  · exact aux_lem_finite_stopping_crude_cost_descendantCell_subset_prefix m z hr nmax w k hk hx

/-- The finite set of leaves, as a finset of the dependent word type. -/
def aux_lem_finite_stopping_crude_cost_leafFinset {m : ℕ} (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax : ℕ) :
    Finset (Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m) := by
  classical
  exact Finset.univ.filter fun p => aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax p.1 p.2

theorem aux_lem_finite_stopping_crude_cost_mem_leafFinset {m : ℕ} (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop)
    (nmax : ℕ) (p : Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m) :
    p ∈ aux_lem_finite_stopping_crude_cost_leafFinset stop nmax ↔ aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax p.1 p.2 := by
  classical
  simp [aux_lem_finite_stopping_crude_cost_leafFinset]

/-- **Stopping-time partition.**  For every stopping rule and final depth, the
leaves of the `(2m+1)`-adic tree give a finite family of actual cells, each a
descendant cube of the root, pairwise disjoint, covering the root up to a null
set, and exhausting all leaves. -/
theorem aux_lem_finite_stopping_crude_cost_stopping_partition (m : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax : ℕ) :
    ∃ (ncell : ℕ) (depth : Fin ncell → ℕ)
      (word : (i : Fin ncell) → Fin (depth i) → OddGridIndex d m),
      (∀ i, aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax (depth i) (word i)) ∧
      (∀ (n : ℕ) (w : Fin n → OddGridIndex d m), aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax n w →
        ∃ i, (⟨depth i, word i⟩ : Σ k, Fin k → OddGridIndex d m) = ⟨n, w⟩) ∧
      Pairwise (fun i j =>
        Disjoint (descendantCell m z hr (depth i) (word i) : Set (SpatialCoordinates d))
          (descendantCell m z hr (depth j) (word j) : Set (SpatialCoordinates d))) ∧
      ((⋃ i, (descendantCell m z hr (depth i) (word i) : Set (SpatialCoordinates d)))
        =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  classical
  let F := aux_lem_finite_stopping_crude_cost_leafFinset stop nmax
  let e : F ≃ Fin F.card := F.equivFin
  let leaf : Fin F.card → Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m :=
    fun i => (e.symm i).1
  have hleaf : ∀ i, aux_lem_finite_stopping_crude_cost_IsLeaf stop nmax (leaf i).1 (leaf i).2 := fun i =>
    (aux_lem_finite_stopping_crude_cost_mem_leafFinset stop nmax _).1 (e.symm i).2
  refine ⟨F.card, fun i => (leaf i).1, fun i => (leaf i).2, hleaf, ?_, ?_, ?_⟩
  · intro n w hw
    have hn : n < nmax + 1 := Nat.lt_succ_of_le hw.1
    let p : Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m := ⟨⟨n, hn⟩, w⟩
    have hp : p ∈ F := (aux_lem_finite_stopping_crude_cost_mem_leafFinset stop nmax p).2 hw
    refine ⟨e ⟨p, hp⟩, ?_⟩
    have hl : leaf (e ⟨p, hp⟩) = p := by
      simp only [leaf]
      rw [e.symm_apply_apply]
    beta_reduce
    rw [hl]
  · intro i j hij
    apply aux_lem_finite_stopping_crude_cost_leaf_cells_disjoint z hr stop nmax (hleaf i) (hleaf j)
    intro heq
    apply hij
    apply e.symm.injective
    apply Subtype.ext
    change leaf i = leaf j
    generalize leaf i = p at heq ⊢
    generalize leaf j = q at heq ⊢
    rcases p with ⟨⟨a, ha⟩, u⟩
    rcases q with ⟨⟨b, hb⟩, v⟩
    simp only [Sigma.mk.inj_iff] at heq
    obtain ⟨rfl, h⟩ := heq
    obtain rfl := eq_of_heq h
    rfl
  · -- cover: the union is inside the root and contains a.e. point of the root
    have hsub : (⋃ i, (descendantCell m z hr (leaf i).1 (leaf i).2 :
        Set (SpatialCoordinates d))) ⊆ centeredCube z r hr :=
      Set.iUnion_subset fun i => aux_lem_finite_stopping_crude_cost_descendantCell_subset_root m z hr _ _
    have hD := aux_lem_finite_stopping_crude_cost_descendantCells_union_ae_eq m z hr nmax
    have hsup : (⋃ w : Fin nmax → OddGridIndex d m,
        (descendantCell m z hr nmax w : Set (SpatialCoordinates d))) ⊆
        ⋃ i, (descendantCell m z hr (leaf i).1 (leaf i).2 : Set (SpatialCoordinates d)) := by
      intro x hx
      obtain ⟨w, hxw⟩ := Set.mem_iUnion.1 hx
      obtain ⟨n, v, hv, hxv⟩ := aux_lem_finite_stopping_crude_cost_exists_leaf_of_mem z hr stop nmax w x hxw
      have hn : n < nmax + 1 := Nat.lt_succ_of_le hv.1
      let p : Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m := ⟨⟨n, hn⟩, v⟩
      have hp : p ∈ F := (aux_lem_finite_stopping_crude_cost_mem_leafFinset stop nmax p).2 hv
      refine Set.mem_iUnion.2 ⟨e ⟨p, hp⟩, ?_⟩
      have hl : leaf (e ⟨p, hp⟩) = p := by
        simp only [leaf]
        rw [e.symm_apply_apply]
      rw [hl]
      exact hxv
    rw [ae_eq_set]
    constructor
    · rw [Set.sdiff_eq_empty.2 hsub, measure_empty]
    · refine measure_mono_null (sdiff_subset_sdiff_right hsup) ?_
      exact (ae_eq_set.1 hD).2


variable {d : ℕ}

/-! ## Poincare witnesses and triadic sides -/

theorem aux_lem_finite_stopping_crude_cost_centeredCube_isOpenBoundedConvexDomain (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    Homogenization.IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  refine ⟨(centeredCube z r hr).isOpen, ?_, ?_⟩
  · refine Homogenization.Bornology.IsBounded.isBoundedDomain ?_
    show Bornology.IsBounded (Metric.ball z (r / 2))
    exact Metric.isBounded_ball
  · show Convex ℝ (Metric.ball z (r / 2))
    exact convex_ball z (r / 2)

/-- Every actual centred cube carries a killed-space Poincare witness. -/
theorem aux_lem_finite_stopping_crude_cost_centeredCube_killedPoincare [NeZero d] (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖ :=
  (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (aux_lem_finite_stopping_crude_cost_centeredCube_isOpenBoundedConvexDomain z hr)).1

/-- Descendant sides of a triadic root in a `3^h`-adic tree are triadic. -/
theorem aux_lem_finite_stopping_crude_cost_descendantSide_zpow (h m : ℕ) (hm : 2 * m + 1 = 3 ^ h) (j : ℤ) (n : ℕ) :
    descendantSide m n ((3 : ℝ) ^ j) = (3 : ℝ) ^ (j - ((h * n : ℕ) : ℤ)) := by
  unfold descendantSide
  have hcast : (2 * (m : ℝ) + 1) = (3 : ℝ) ^ h := by exact_mod_cast hm
  rw [hcast, ← pow_mul, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]

/-! ## Refinement of partitions -/

/-- A partition of every cell of a partition is a partition. -/
theorem aux_lem_finite_stopping_crude_cost_partition_refine {X : Type*} [MeasurableSpace X] {μ : Measure X} {Q : Set X}
    {ι : Type*} [Countable ι] (R : ι → Set X)
    (hRdisj : Pairwise (fun a b => Disjoint (R a) (R b)))
    (hRcov : (⋃ a, R a) =ᵐ[μ] Q)
    {κ : ι → Type*} [∀ a, Countable (κ a)] (q : (a : ι) → κ a → Set X)
    (hqR : ∀ a b, q a b ⊆ R a)
    (hqdisj : ∀ a, Pairwise (fun b b' => Disjoint (q a b) (q a b')))
    (hqcov : ∀ a, (⋃ b, q a b) =ᵐ[μ] R a) :
    Pairwise (fun p p' : (Σ a, κ a) => Disjoint (q p.1 p.2) (q p'.1 p'.2)) ∧
      (⋃ p : (Σ a, κ a), q p.1 p.2) =ᵐ[μ] Q := by
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ hne
    by_cases haa : a = a'
    · subst haa
      have hbb : b ≠ b' := fun h => hne (by rw [h])
      exact hqdisj a hbb
    · exact (hRdisj haa).mono (hqR a b) (hqR a' b')
  · rw [Set.iUnion_sigma]
    exact (EventuallyEqSet.countable_iUnion hqcov).trans hRcov

/-! ## Actual cell energies -/

variable {Q U : Opens (SpatialCoordinates d)}

/-- The root energy density integrated over a set. -/
def aux_lem_finite_stopping_crude_cost_energyOn (a : PositiveCoefficient Q) (u : SobolevData Q)
    (s : Set (SpatialCoordinates d)) : ℝ :=
  ∑ j : Fin d, ∫ x in s, a.val x * (u.2 j x * u.2 j x)

theorem aux_lem_finite_stopping_crude_cost_integrableOn_energy_integrand (a : PositiveCoefficient Q) (u : SobolevData Q)
    (j : Fin d) :
    IntegrableOn (fun x => a.val x * (u.2 j x * u.2 j x)) (Q : Set (SpatialCoordinates d))
      volume := by
  obtain ⟨C, hC⟩ := coeff_ae_bound a
  exact integrableOn_coeff_mul (Lp.memLp a.val).aestronglyMeasurable hC
    (Lp.memLp (u.2 j)) (Lp.memLp (u.2 j))

theorem aux_lem_finite_stopping_crude_cost_energy_integrand_nonneg_ae (a : PositiveCoefficient Q) (u : SobolevData Q)
    (j : Fin d) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      0 ≤ a.val x * (u.2 j x * u.2 j x) := by
  obtain ⟨c, hc, ha⟩ := a.property
  filter_upwards [ha] with x hx
  exact mul_nonneg (hc.le.trans hx) (mul_self_nonneg _)

theorem aux_lem_finite_stopping_crude_cost_sobolevCoefficientForm_self_eq_energyOn (a : PositiveCoefficient Q)
    (u : SobolevData Q) :
    sobolevCoefficientForm a u u = aux_lem_finite_stopping_crude_cost_energyOn a u (Q : Set (SpatialCoordinates d)) :=
  sobolevCoefficientForm_apply a u u

/-- The literal restricted energy is the set integral of the root density. -/
theorem aux_lem_finite_stopping_crude_cost_restrict_energy_eq (hU : U ≤ Q) (a : PositiveCoefficient Q) (u : SobolevData Q) :
    sobolevCoefficientForm (positiveCoefficientRestrict hU a) (sobolevDataRestrict hU u)
      (sobolevDataRestrict hU u) = aux_lem_finite_stopping_crude_cost_energyOn a u (U : Set (SpatialCoordinates d)) := by
  rw [sobolevCoefficientForm_apply]
  unfold aux_lem_finite_stopping_crude_cost_energyOn
  refine Finset.sum_congr rfl fun j _ => ?_
  apply integral_congr_ae
  filter_upwards [positiveCoefficientRestrict_coeFn hU a,
    domainLpRestrict_coeFn hU (u.2 j)] with x ha hu
  change (positiveCoefficientRestrict hU a).val x *
      ((domainLpRestrict hU (u.2 j)) x * (domainLpRestrict hU (u.2 j)) x) = _
  rw [ha, hu]

theorem aux_lem_finite_stopping_crude_cost_energyOn_nonneg (a : PositiveCoefficient Q) (u : SobolevData Q)
    {s : Set (SpatialCoordinates d)} (hs : s ⊆ Q) : 0 ≤ aux_lem_finite_stopping_crude_cost_energyOn a u s := by
  refine Finset.sum_nonneg fun j _ => integral_nonneg_of_ae ?_
  exact ae_restrict_of_ae_restrict_of_subset hs (aux_lem_finite_stopping_crude_cost_energy_integrand_nonneg_ae a u j)

theorem aux_lem_finite_stopping_crude_cost_energyOn_mono (a : PositiveCoefficient Q) (u : SobolevData Q)
    {s t : Set (SpatialCoordinates d)} (hst : s ⊆ t) (ht : t ⊆ Q) :
    aux_lem_finite_stopping_crude_cost_energyOn a u s ≤ aux_lem_finite_stopping_crude_cost_energyOn a u t := by
  refine Finset.sum_le_sum fun j _ => ?_
  exact setIntegral_mono_set ((aux_lem_finite_stopping_crude_cost_integrableOn_energy_integrand a u j).mono_set ht)
    (ae_restrict_of_ae_restrict_of_subset ht (aux_lem_finite_stopping_crude_cost_energy_integrand_nonneg_ae a u j))
    (Eventually.of_forall hst)

/-- Energies of disjoint measurable subsets add below the root energy. -/
theorem aux_lem_finite_stopping_crude_cost_energyOn_sum_le {ι : Type*} (F : Finset ι) (a : PositiveCoefficient Q)
    (u : SobolevData Q) (s : ι → Set (SpatialCoordinates d))
    (hs : ∀ i, MeasurableSet (s i)) (hsQ : ∀ i, s i ⊆ Q)
    (hdisj : (F : Set ι).PairwiseDisjoint s) :
    (∑ i ∈ F, aux_lem_finite_stopping_crude_cost_energyOn a u (s i)) ≤ aux_lem_finite_stopping_crude_cost_energyOn a u (Q : Set (SpatialCoordinates d)) := by
  have hunion : (∑ i ∈ F, aux_lem_finite_stopping_crude_cost_energyOn a u (s i)) = aux_lem_finite_stopping_crude_cost_energyOn a u (⋃ i ∈ F, s i) := by
    unfold aux_lem_finite_stopping_crude_cost_energyOn
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_biUnion_finset F (fun i _ => hs i) hdisj
      (fun i _ => (aux_lem_finite_stopping_crude_cost_integrableOn_energy_integrand a u j).mono_set (hsQ i))]
  rw [hunion]
  exact aux_lem_finite_stopping_crude_cost_energyOn_mono a u (Set.iUnion₂_subset fun i _ => hsQ i) le_rfl

/-- On an a.e. partition, the cell energies sum exactly to the root energy. -/
theorem aux_lem_finite_stopping_crude_cost_energyOn_sum_eq {ι : Type*} [Fintype ι] (a : PositiveCoefficient Q)
    (u : SobolevData Q) (s : ι → Set (SpatialCoordinates d))
    (hs : ∀ i, MeasurableSet (s i)) (hsQ : ∀ i, s i ⊆ Q)
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcov : (⋃ i, s i) =ᵐ[volume] (Q : Set (SpatialCoordinates d))) :
    (∑ i, aux_lem_finite_stopping_crude_cost_energyOn a u (s i)) = aux_lem_finite_stopping_crude_cost_energyOn a u (Q : Set (SpatialCoordinates d)) := by
  unfold aux_lem_finite_stopping_crude_cost_energyOn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← setIntegral_congr_set hcov]
  exact (integral_iUnion_fintype hs hdisj
    (fun i => (aux_lem_finite_stopping_crude_cost_integrableOn_energy_integrand a u j).mono_set (hsQ i))).symm

/-- Volumes of disjoint measurable subsets add below the root volume. -/
theorem aux_lem_finite_stopping_crude_cost_volume_sum_le {ι : Type*} (F : Finset ι) (s : ι → Set (SpatialCoordinates d))
    (hs : ∀ i, MeasurableSet (s i)) (hsQ : ∀ i, s i ⊆ Q)
    (hdisj : (F : Set ι).PairwiseDisjoint s)
    (hQ : volume (Q : Set (SpatialCoordinates d)) ≠ ⊤) :
    (∑ i ∈ F, volume.real (s i)) ≤ volume.real (Q : Set (SpatialCoordinates d)) := by
  rw [← measureReal_biUnion_finset hdisj (fun i _ => hs i)
    (fun i _ => ne_top_of_le_ne_top hQ (measure_mono (hsQ i)))]
  exact measureReal_mono (Set.iUnion₂_subset fun i _ => hsQ i) hQ

/-- The Dirichlet principle on a cell: the response with the literal restricted
datum is at most the literal restricted energy. -/
theorem aux_lem_finite_stopping_crude_cost_dirichletResponse_restrict_le_energyOn (hU : U ≤ Q)
    (hPU : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph U,
      ‖(v : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) v‖)
    (a : PositiveCoefficient Q) (u : weakSobolevGraph Q) :
    dirichletResponse (killedResponseSpace hPU) (positiveCoefficientRestrict hU a)
        ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩ ≤
      aux_lem_finite_stopping_crude_cost_energyOn a u.val (U : Set (SpatialCoordinates d)) := by
  have h := (dirichletResponse_isLeast (killedResponseSpace hPU)
    (positiveCoefficientRestrict hU a)
    ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩).2
    (Set.mem_range_self (0 : (killedResponseSpace hPU).space))
  simp only [ZeroMemClass.coe_zero, add_zero] at h
  rw [← aux_lem_finite_stopping_crude_cost_restrict_energy_eq hU a u.val]
  exact h

/-- The response of the root is the root energy of its minimizer. -/
theorem aux_lem_finite_stopping_crude_cost_dirichletResponse_eq_energyOn (S : ResponseSpace Q) (a : PositiveCoefficient Q)
    (b : weakSobolevGraph Q) :
    dirichletResponse S a b =
      aux_lem_finite_stopping_crude_cost_energyOn a (dirichletMinimizer S a b).val (Q : Set (SpatialCoordinates d)) :=
  aux_lem_finite_stopping_crude_cost_sobolevCoefficientForm_self_eq_energyOn a _


/-- Least window index `⌈N / (4 H1)⌉`. -/
def aux_lem_finite_stopping_crude_cost_obsLo (H1 N : ℕ) : ℕ := (N + (4 * H1 - 1)) / (4 * H1)

/-- Greatest window index `⌊3N / (4 H1)⌋`. -/
def aux_lem_finite_stopping_crude_cost_obsHi (H1 N : ℕ) : ℕ := 3 * N / (4 * H1)

/-- Initial triadic depth `H1 aux_lem_finite_stopping_crude_cost_obsLo + j`. -/
def aux_lem_finite_stopping_crude_cost_obsT0 (H1 N : ℕ) (j : ℤ) : ℕ := (((H1 * aux_lem_finite_stopping_crude_cost_obsLo H1 N : ℕ) : ℤ) + j).toNat

/-- Number of stage-2 levels. -/
def aux_lem_finite_stopping_crude_cost_obsB (H1 N : ℕ) : ℕ := aux_lem_finite_stopping_crude_cost_obsHi H1 N - aux_lem_finite_stopping_crude_cost_obsLo H1 N

theorem aux_lem_finite_stopping_crude_cost_obsLo_le_iff {H1 : ℕ} (hH1 : 0 < H1) (N n : ℕ) :
    aux_lem_finite_stopping_crude_cost_obsLo H1 N ≤ n ↔ N ≤ 4 * (H1 * n) := by
  have hK : 0 < 4 * H1 := by omega
  unfold aux_lem_finite_stopping_crude_cost_obsLo
  rw [Nat.div_le_iff_le_mul_add_pred hK, ← mul_assoc]
  generalize 4 * H1 * n = X
  omega

theorem aux_lem_finite_stopping_crude_cost_le_obsHi_iff {H1 : ℕ} (hH1 : 0 < H1) (N n : ℕ) :
    n ≤ aux_lem_finite_stopping_crude_cost_obsHi H1 N ↔ 4 * (H1 * n) ≤ 3 * N := by
  have hK : 0 < 4 * H1 := by omega
  unfold aux_lem_finite_stopping_crude_cost_obsHi
  rw [Nat.le_div_iff_mul_le hK]
  constructor <;> intro h <;> linarith [mul_comm n (4 * H1), mul_assoc 4 H1 n]

theorem aux_lem_finite_stopping_crude_cost_window_iff {H1 : ℕ} (hH1 : 0 < H1) (N n : ℕ) :
    (N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N) ↔ n ∈ Finset.Icc (aux_lem_finite_stopping_crude_cost_obsLo H1 N) (aux_lem_finite_stopping_crude_cost_obsHi H1 N) := by
  rw [Finset.mem_Icc, aux_lem_finite_stopping_crude_cost_obsLo_le_iff hH1, aux_lem_finite_stopping_crude_cost_le_obsHi_iff hH1]

theorem aux_lem_finite_stopping_crude_cost_four_H1_obsLo_ge {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) : N ≤ 4 * (H1 * aux_lem_finite_stopping_crude_cost_obsLo H1 N) :=
  (aux_lem_finite_stopping_crude_cost_obsLo_le_iff hH1 N _).1 le_rfl

theorem aux_lem_finite_stopping_crude_cost_four_H1_obsHi_le {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) : 4 * (H1 * aux_lem_finite_stopping_crude_cost_obsHi H1 N) ≤ 3 * N :=
  (aux_lem_finite_stopping_crude_cost_le_obsHi_iff hH1 N _).1 le_rfl

theorem aux_lem_finite_stopping_crude_cost_four_H1_obsLo_le {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) :
    4 * (H1 * aux_lem_finite_stopping_crude_cost_obsLo H1 N) ≤ N + 4 * H1 := by
  have h := Nat.div_mul_le_self (N + (4 * H1 - 1)) (4 * H1)
  unfold aux_lem_finite_stopping_crude_cost_obsLo
  have : (N + (4 * H1 - 1)) / (4 * H1) * (4 * H1) = 4 * (H1 * ((N + (4 * H1 - 1)) / (4 * H1))) := by
    ring
  omega

theorem aux_lem_finite_stopping_crude_cost_four_H1_obsHi_gt {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) :
    3 * N < 4 * (H1 * aux_lem_finite_stopping_crude_cost_obsHi H1 N) + 4 * H1 := by
  have hK : 0 < 4 * H1 := by omega
  have h := Nat.lt_mul_div_succ (3 * N) hK
  unfold aux_lem_finite_stopping_crude_cost_obsHi
  have : 4 * H1 * (3 * N / (4 * H1) + 1) = 4 * (H1 * (3 * N / (4 * H1))) + 4 * H1 := by ring
  omega

theorem aux_lem_finite_stopping_crude_cost_obsLo_le_obsHi {H1 : ℕ} (hH1 : 0 < H1) {N : ℕ} (hN : 4 * H1 ≤ N) :
    aux_lem_finite_stopping_crude_cost_obsLo H1 N ≤ aux_lem_finite_stopping_crude_cost_obsHi H1 N := by
  rw [aux_lem_finite_stopping_crude_cost_obsLo_le_iff hH1]
  have h1 := aux_lem_finite_stopping_crude_cost_four_H1_obsHi_gt hH1 N
  omega

theorem aux_lem_finite_stopping_crude_cost_obsT0_eq {H1 : ℕ} (hH1 : 0 < H1) {N : ℕ} {j : ℤ} (hN : 4 * j.natAbs ≤ N) :
    (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j : ℤ) = ((H1 * aux_lem_finite_stopping_crude_cost_obsLo H1 N : ℕ) : ℤ) + j := by
  unfold aux_lem_finite_stopping_crude_cost_obsT0
  apply Int.toNat_of_nonneg
  have h := aux_lem_finite_stopping_crude_cost_four_H1_obsLo_ge hH1 N
  have h2 : j.natAbs ≤ H1 * aux_lem_finite_stopping_crude_cost_obsLo H1 N := by omega
  have h3 : -(j.natAbs : ℤ) ≤ j := by omega
  omega

/-- The window has `B + 1` levels. -/
theorem aux_lem_finite_stopping_crude_cost_card_window {H1 : ℕ} (hH1 : 0 < H1) {N : ℕ} (hN : 4 * H1 ≤ N) :
    Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} = aux_lem_finite_stopping_crude_cost_obsB H1 N + 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (aux_lem_finite_stopping_crude_cost_window_iff hH1 N)), Nat.card_eq_fintype_card,
    Fintype.card_coe, Nat.card_Icc, aux_lem_finite_stopping_crude_cost_obsB]
  have := aux_lem_finite_stopping_crude_cost_obsLo_le_obsHi hH1 hN
  omega

open Classical in
/-- The selected window levels: at most one more than the selected stage-2 levels. -/
theorem aux_lem_finite_stopping_crude_cost_card_selected_window_le {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) (S : ℕ → Prop) :
    Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} ≤
      ((Finset.univ : Finset (Fin (aux_lem_finite_stopping_crude_cost_obsB H1 N))).filter
        (fun i => S (aux_lem_finite_stopping_crude_cost_obsLo H1 N + (i.val + 1)))).card + 1 := by
  classical
  set a := aux_lem_finite_stopping_crude_cost_obsLo H1 N
  set b := aux_lem_finite_stopping_crude_cost_obsHi H1 N
  have hiff : ∀ n, (S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N) ↔
      n ∈ (Finset.Icc a b).filter S := by
    intro n
    rw [Finset.mem_filter, ← aux_lem_finite_stopping_crude_cost_window_iff hH1]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card,
    Fintype.card_coe]
  have hsub : (Finset.Icc a b).filter S ⊆
      insert a (((Finset.univ : Finset (Fin (aux_lem_finite_stopping_crude_cost_obsB H1 N))).filter
        (fun i => S (a + (i.val + 1)))).image (fun i => a + (i.val + 1))) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases Nat.eq_or_lt_of_le hn.1.1 with h | h
    · exact Finset.mem_insert.2 (Or.inl h.symm)
    · refine Finset.mem_insert.2 (Or.inr ?_)
      rw [Finset.mem_image]
      have hlt : n - a - 1 < aux_lem_finite_stopping_crude_cost_obsB H1 N := by unfold aux_lem_finite_stopping_crude_cost_obsB; omega
      refine ⟨⟨n - a - 1, hlt⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have : a + (n - a - 1 + 1) = n := by omega
        simp only [this]
        exact hn.2
      · simp only
        omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_insert_le _ _
    _ ≤ _ := Nat.add_le_add_right Finset.card_image_le _

/-- Stage-2 sides are the absolute triadic sides `3^(-H1 (aux_lem_finite_stopping_crude_cost_obsLo + s))`. -/
theorem aux_lem_finite_stopping_crude_cost_stage_side_eq {H1 : ℕ} (hH1 : 0 < H1) {N : ℕ} {j : ℤ} (hN : 4 * j.natAbs ≤ N)
    (s : ℕ) :
    descendantSide (subdivisionHalfWidth H1) s
        (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j)) =
      (3 : ℝ) ^ (-((H1 * (aux_lem_finite_stopping_crude_cost_obsLo H1 N + s) : ℕ) : ℤ)) := by
  rw [aux_lem_finite_stopping_crude_cost_descendantSide_zpow 1 1 (by norm_num) j, aux_lem_finite_stopping_crude_cost_descendantSide_zpow H1 _
    (two_mul_subdivisionHalfWidth_add_one H1)]
  congr 1
  have h := aux_lem_finite_stopping_crude_cost_obsT0_eq hH1 (N := N) (j := j) hN
  push_cast at h ⊢
  rw [one_mul, h]
  ring


variable {d : ℕ}

/-- The stage-2 cell of word `w` at depth `s` inside the initial cell `w0`. -/
def aux_lem_finite_stopping_crude_cost_cell2 (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    Opens (SpatialCoordinates d) :=
  descendantCell mg (descendantCenter 1 z r t0 w0) (descendantSide_pos 1 t0 hr) s w

theorem aux_lem_finite_stopping_crude_cost_cell2_eq_centeredCube (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 s w =
      centeredCube (descendantCenter mg (descendantCenter 1 z r t0 w0)
        (descendantSide 1 t0 r) s w)
        (descendantSide mg s (descendantSide 1 t0 r))
        (descendantSide_pos mg s (descendantSide_pos 1 t0 hr)) := rfl

theorem aux_lem_finite_stopping_crude_cost_cell2_subset_initial (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    (aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 s w : Set (SpatialCoordinates d)) ⊆
      descendantCell 1 z hr t0 w0 :=
  aux_lem_finite_stopping_crude_cost_descendantCell_subset_root mg _ _ s w

theorem aux_lem_finite_stopping_crude_cost_cell2_subset_root (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    (aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 s w : Set (SpatialCoordinates d)) ⊆ centeredCube z r hr :=
  (aux_lem_finite_stopping_crude_cost_cell2_subset_initial z hr t0 mg w0 s w).trans (aux_lem_finite_stopping_crude_cost_descendantCell_subset_root 1 z hr t0 w0)

theorem aux_lem_finite_stopping_crude_cost_cell2_le_root (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 s w ≤ centeredCube z r hr :=
  aux_lem_finite_stopping_crude_cost_cell2_subset_root z hr t0 mg w0 s w

/-- The two-stage leaf index type. -/
abbrev aux_lem_finite_stopping_crude_cost_LeafIdx (d t0 mg B : ℕ) :=
  (Fin t0 → OddGridIndex d 1) × (Σ s : Fin (B + 1), Fin s → OddGridIndex d mg)

/-- The two-stage leaves. -/
def aux_lem_finite_stopping_crude_cost_leaves2 {t0 mg : ℕ}
    (stop : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
    (B : ℕ) : Finset (aux_lem_finite_stopping_crude_cost_LeafIdx d t0 mg B) := by
  classical
  exact Finset.univ.filter fun p => aux_lem_finite_stopping_crude_cost_IsLeaf (stop p.1) B p.2.1 p.2.2

theorem aux_lem_finite_stopping_crude_cost_mem_leaves2 {t0 mg : ℕ}
    (stop : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
    (B : ℕ) (p : aux_lem_finite_stopping_crude_cost_LeafIdx d t0 mg B) :
    p ∈ aux_lem_finite_stopping_crude_cost_leaves2 stop B ↔ aux_lem_finite_stopping_crude_cost_IsLeaf (stop p.1) B p.2.1 p.2.2 := by
  classical
  simp [aux_lem_finite_stopping_crude_cost_leaves2]

/-- The cell of a two-stage leaf index. -/
def aux_lem_finite_stopping_crude_cost_leafCell (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) {t0 mg B : ℕ}
    (p : aux_lem_finite_stopping_crude_cost_LeafIdx d t0 mg B) : Opens (SpatialCoordinates d) :=
  aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg p.1 p.2.1 p.2.2

theorem aux_lem_finite_stopping_crude_cost_leaves2_pairwiseDisjoint (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {t0 mg : ℕ}
    (stop : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
    (B : ℕ) :
    ((aux_lem_finite_stopping_crude_cost_leaves2 stop B : Finset (aux_lem_finite_stopping_crude_cost_LeafIdx d t0 mg B)) : Set (aux_lem_finite_stopping_crude_cost_LeafIdx d t0 mg B)).PairwiseDisjoint
      (fun p => (aux_lem_finite_stopping_crude_cost_leafCell z hr p : Set (SpatialCoordinates d))) := by
  rintro ⟨w0, q⟩ hp ⟨w0', q'⟩ hp' hne
  simp only [Finset.mem_coe, aux_lem_finite_stopping_crude_cost_mem_leaves2] at hp hp'
  show Disjoint (aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 q.1 q.2 : Set (SpatialCoordinates d))
    (aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0' q'.1 q'.2 : Set (SpatialCoordinates d))
  by_cases hw0 : w0 = w0'
  · subst hw0
    have hqq : q ≠ q' := fun h => hne (by rw [h])
    apply aux_lem_finite_stopping_crude_cost_leaf_cells_disjoint _ _ (stop w0) B hp hp'
    intro heq
    apply hqq
    rcases q with ⟨⟨a, ha⟩, v⟩
    rcases q' with ⟨⟨b, hb⟩, v'⟩
    simp only [Sigma.mk.inj_iff] at heq
    obtain ⟨rfl, h⟩ := heq
    obtain rfl := eq_of_heq h
    rfl
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact hw0 (aux_lem_finite_stopping_crude_cost_descendantCell_word_eq_of_mem 1 z hr t0 w0 w0' x
      (aux_lem_finite_stopping_crude_cost_cell2_subset_initial z hr t0 mg w0 _ _ hx) (aux_lem_finite_stopping_crude_cost_cell2_subset_initial z hr t0 mg w0' _ _ hx'))

theorem aux_lem_finite_stopping_crude_cost_leaves2_cover (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) {t0 mg : ℕ}
    (stop : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
    (B : ℕ) :
    (⋃ p ∈ aux_lem_finite_stopping_crude_cost_leaves2 stop B, (aux_lem_finite_stopping_crude_cost_leafCell z hr p : Set (SpatialCoordinates d))) =ᵐ[volume]
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  classical
  have h1 := aux_lem_finite_stopping_crude_cost_descendantCells_union_ae_eq 1 z hr t0
  have h2 : ∀ w0 : Fin t0 → OddGridIndex d 1,
      (⋃ w : Fin B → OddGridIndex d mg,
        (aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 B w : Set (SpatialCoordinates d))) =ᵐ[volume]
        (descendantCell 1 z hr t0 w0 : Set (SpatialCoordinates d)) := fun w0 =>
    aux_lem_finite_stopping_crude_cost_descendantCells_union_ae_eq mg _ (descendantSide_pos 1 t0 hr) B
  have h3 := (EventuallyEqSet.countable_iUnion h2).trans h1
  have hsub : (⋃ p ∈ aux_lem_finite_stopping_crude_cost_leaves2 stop B, (aux_lem_finite_stopping_crude_cost_leafCell z hr p : Set (SpatialCoordinates d))) ⊆
      centeredCube z r hr :=
    Set.iUnion₂_subset fun p _ => aux_lem_finite_stopping_crude_cost_cell2_subset_root z hr t0 mg _ _ _
  have hsup : (⋃ w0 : Fin t0 → OddGridIndex d 1, ⋃ w : Fin B → OddGridIndex d mg,
      (aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 B w : Set (SpatialCoordinates d))) ⊆
      ⋃ p ∈ aux_lem_finite_stopping_crude_cost_leaves2 stop B, (aux_lem_finite_stopping_crude_cost_leafCell z hr p : Set (SpatialCoordinates d)) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w0, w, hxw⟩ := hx
    obtain ⟨n, v, hv, hxv⟩ := aux_lem_finite_stopping_crude_cost_exists_leaf_of_mem _ (descendantSide_pos 1 t0 hr)
      (stop w0) B w x hxw
    have hn : n < B + 1 := Nat.lt_succ_of_le hv.1
    let p : aux_lem_finite_stopping_crude_cost_LeafIdx d t0 mg B := (w0, ⟨⟨n, hn⟩, v⟩)
    have hp : p ∈ aux_lem_finite_stopping_crude_cost_leaves2 stop B := (aux_lem_finite_stopping_crude_cost_mem_leaves2 stop B p).2 hv
    exact Set.mem_biUnion hp hxv
  rw [ae_eq_set]
  constructor
  · rw [Set.sdiff_eq_empty.2 hsub, measure_empty]
  · exact measure_mono_null (sdiff_subset_sdiff_right hsup) (ae_eq_set.1 h3).2

/-- Target response on a subdomain, with the literal restricted datum and coefficient. -/
def aux_lem_finite_stopping_crude_cost_respOn {Q U : Opens (SpatialCoordinates d)} (aT : PositiveCoefficient Q)
    (u : weakSobolevGraph Q) (hU : U ≤ Q)
    (hPU : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph U,
      ‖(v : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) v‖) : ℝ :=
  dirichletResponse (killedResponseSpace hPU) (positiveCoefficientRestrict hU aT)
    ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩

theorem aux_lem_finite_stopping_crude_cost_cell2_killedPoincare [NeZero d] (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 s w),
      ‖(v : SobolevData (aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 s w)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (aux_lem_finite_stopping_crude_cost_cell2 z hr t0 mg w0 s w)) v‖ :=
  aux_lem_finite_stopping_crude_cost_centeredCube_killedPoincare _ (descendantSide_pos mg s (descendantSide_pos 1 t0 hr))


theorem aux_lem_finite_stopping_crude_cost_c2Norm_nonneg {d : ℕ} (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    0 ≤ c2Norm S f := by
  unfold c2Norm
  refine add_nonneg (add_nonneg ?_ ?_) ?_ <;>
    exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; positivity)



variable {d : ℕ}

/-- Two points of a closed sup-norm cube of side `s` are at Euclidean distance at most
`√d s`. -/
theorem aux_lem_finite_stopping_crude_cost_euclid_le (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (x y : SpatialCoordinates d)
    (hx : x ∈ closure (Metric.ball c (s / 2)))
    (hy : y ∈ closure (Metric.ball c (s / 2))) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * s := by
  have hcl : closure (Metric.ball c (s / 2)) ⊆ Metric.closedBall c (s / 2) :=
    Metric.closure_ball_subset_closedBall
  have hxy : dist x y ≤ s := by
    have h1 := hcl hx
    have h2 := hcl hy
    rw [Metric.mem_closedBall] at h1 h2
    calc dist x y ≤ dist x c + dist y c := dist_triangle_right x y c
      _ ≤ s / 2 + s / 2 := add_le_add h1 h2
      _ = s := by ring
  have hcoord : ∀ j : Fin d, (x j - y j) ^ 2 ≤ s ^ 2 := by
    intro j
    have hj : |x j - y j| ≤ s := by
      have := dist_le_pi_dist x y j
      rw [Real.dist_eq] at this
      linarith
    have h0 : 0 ≤ |x j - y j| := abs_nonneg _
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ s ^ 2 := pow_le_pow_left₀ h0 hj 2
  have hsum : ∑ j : Fin d, (x j - y j) ^ 2 ≤ (d : ℝ) * s ^ 2 := by
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, s ^ 2 :=
          Finset.sum_le_sum fun j _ => hcoord j
      _ = (d : ℝ) * s ^ 2 := by simp
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * s ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * s := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hs.le]

theorem aux_lem_finite_stopping_crude_cost_holderSeminorm_nonneg (β : ℝ) (S : Set (SpatialCoordinates d))
    (U : SpatialCoordinates d → ℝ) : 0 ≤ holderSeminorm β S U := by
  apply Real.sSup_nonneg
  rintro v ⟨x, -, y, -, -, rfl⟩
  exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

theorem aux_lem_finite_stopping_crude_cost_holderSeminorm_le_cAlphaNorm (α : ℝ) (S : Set (SpatialCoordinates d))
    (U : SpatialCoordinates d → ℝ) : holderSeminorm α S U ≤ cAlphaNorm α S U := by
  unfold cAlphaNorm
  have h0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |U x|} := by
    apply Real.sSup_nonneg
    rintro v ⟨x, -, rfl⟩
    exact abs_nonneg _
  linarith

/-- Hölder downgrade: `C^α` on `S` gives `C^β` (`0 ≤ β ≤ α`) on any `S' ⊆ S` of
Euclidean diameter `≤ D`, with `[U]_{β,S'} ≤ [U]_{α,S} D^(α-β)`. -/
theorem aux_lem_finite_stopping_crude_cost_holder_downgrade {α β D : ℝ} (hβα : β ≤ α) (hD : 0 ≤ D)
    {S S' : Set (SpatialCoordinates d)} (hS' : S' ⊆ S) (U : SpatialCoordinates d → ℝ)
    (hU : IsHolderOn α S U)
    (hdiam : ∀ x ∈ S', ∀ y ∈ S', Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ D) :
    IsHolderOn β S' U ∧ holderSeminorm β S' U ≤ holderSeminorm α S U * D ^ (α - β) := by
  have hHα := aux_lem_finite_stopping_crude_cost_holderSeminorm_nonneg α S U
  have hbound : ∀ v ∈ holderRatioSet β S' U, v ≤ holderSeminorm α S U * D ^ (α - β) := by
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with he
    have hepos : 0 < e := by
      rw [he, Real.sqrt_pos]
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra hall
        push Not at hall
        exact hxy (funext hall)
      have hj2 : 0 < (x j - y j) ^ 2 := by
        have : x j - y j ≠ 0 := sub_ne_zero.mpr hj
        positivity
      exact lt_of_lt_of_le hj2
        (Finset.single_le_sum (fun i _ => sq_nonneg (x i - y i)) (Finset.mem_univ j))
    have hmem : |U x - U y| / e ^ α ∈ holderRatioSet α S U :=
      ⟨x, hS' hx, y, hS' hy, hxy, rfl⟩
    have hA : |U x - U y| / e ^ α ≤ holderSeminorm α S U := le_csSup hU hmem
    have hA0 : 0 ≤ |U x - U y| / e ^ α :=
      div_nonneg (abs_nonneg _) (Real.rpow_nonneg hepos.le _)
    have hsplit : |U x - U y| / e ^ β = (|U x - U y| / e ^ α) * e ^ (α - β) := by
      rw [Real.rpow_sub hepos]
      have h1 : 0 < e ^ α := Real.rpow_pos_of_pos hepos _
      have h2 : 0 < e ^ β := Real.rpow_pos_of_pos hepos _
      field_simp
    have hB : e ^ (α - β) ≤ D ^ (α - β) :=
      Real.rpow_le_rpow hepos.le (hdiam x hx y hy) (by linarith)
    have hB0 : 0 ≤ e ^ (α - β) := Real.rpow_nonneg hepos.le _
    rw [hsplit]
    exact mul_le_mul hA hB hB0 hHα
  have hR0 : 0 ≤ holderSeminorm α S U * D ^ (α - β) :=
    mul_nonneg hHα (Real.rpow_nonneg hD _)
  exact ⟨⟨_, hbound⟩, Real.sSup_le hbound hR0⟩

/-- The frontier of a subcube lies in the closed root. -/
theorem aux_lem_finite_stopping_crude_cost_frontier_subset_closedCube {z c : SpatialCoordinates d} {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ) (hle : centeredCube c ρ hρ ≤ centeredCube z R hR) :
    frontier (centeredCube c ρ hρ : Set (SpatialCoordinates d)) ⊆
      (closedCube z R hR : Set (SpatialCoordinates d)) := by
  refine frontier_subset_closure.trans ?_
  have hsub : (centeredCube c ρ hρ : Set (SpatialCoordinates d)) ⊆
      (closedCube z R hR : Set (SpatialCoordinates d)) :=
    (show (centeredCube c ρ hρ : Set (SpatialCoordinates d)) ⊆ centeredCube z R hR from hle).trans
      (centeredCube_subset_closedCube z hR)
  exact (closure_mono hsub).trans (Metric.isClosed_closedBall.closure_subset)

/-- Points of the frontier of a subcube of side `ρ` are within Euclidean `√d ρ`. -/
theorem aux_lem_finite_stopping_crude_cost_frontier_euclid_le {c : SpatialCoordinates d} {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ x ∈ frontier (centeredCube c ρ hρ : Set (SpatialCoordinates d)),
    ∀ y ∈ frontier (centeredCube c ρ hρ : Set (SpatialCoordinates d)),
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * ρ := by
  intro x hx y hy
  exact aux_lem_finite_stopping_crude_cost_euclid_le c ρ hρ x y (frontier_subset_closure hx) (frontier_subset_closure hy)

/-- The pure-real crude-cost inequality. -/
theorem aux_lem_finite_stopping_crude_cost_crude_real {C1 Lam Ke Kg g Hα X ρ α β η σ : ℝ} (hd : 1 ≤ d)
    (hC1 : 0 ≤ C1) (hLam0 : 0 ≤ Lam) (hLam : Lam ≤ Ke * ρ ^ (-η))
    (hX0 : 0 ≤ X) (hX : X ≤ Hα * (Real.sqrt d * ρ) ^ (α - β))
    (hHα0 : 0 ≤ Hα) (hHα : Hα ≤ Kg * g)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hαβ1 : α - β ≤ 1)
    (hσ : 2 - 2 * α + η ≤ σ) :
    C1 * Lam * ρ ^ ((d : ℝ) - 2) * (ρ ^ β * X) ^ 2 ≤
      C1 * (d : ℝ) * Ke * Kg ^ 2 * ρ ^ ((d : ℝ) - σ) * g ^ 2 := by
  have hsd1 : 1 ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hρβ : 0 < ρ ^ β := Real.rpow_pos_of_pos hρ _
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ _
  have hpow1 : (Real.sqrt d) ^ (α - β) ≤ Real.sqrt d := by
    calc (Real.sqrt d) ^ (α - β) ≤ (Real.sqrt d) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hsd1 hαβ1
      _ = Real.sqrt d := Real.rpow_one _
  have hpow0 : 0 ≤ (Real.sqrt d) ^ (α - β) := Real.rpow_nonneg hsd0 _
  -- the Hölder factor
  have hY0 : 0 ≤ ρ ^ β * X := mul_nonneg hρβ.le hX0
  have hY : ρ ^ β * X ≤ Hα * (Real.sqrt d) ^ (α - β) * ρ ^ α := by
    have h1 : ρ ^ β * X ≤ ρ ^ β * (Hα * (Real.sqrt d * ρ) ^ (α - β)) :=
      mul_le_mul_of_nonneg_left hX hρβ.le
    have h2 : ρ ^ β * (Hα * (Real.sqrt d * ρ) ^ (α - β)) =
        Hα * (Real.sqrt d) ^ (α - β) * ρ ^ α := by
      rw [Real.mul_rpow hsd0 hρ.le]
      have : ρ ^ β * ρ ^ (α - β) = ρ ^ α := by
        rw [← Real.rpow_add hρ]; congr 1; ring
      calc ρ ^ β * (Hα * ((Real.sqrt d) ^ (α - β) * ρ ^ (α - β))) =
          Hα * (Real.sqrt d) ^ (α - β) * (ρ ^ β * ρ ^ (α - β)) := by ring
        _ = _ := by rw [this]
    linarith
  have hY2 : (ρ ^ β * X) ^ 2 ≤ (Kg * g) ^ 2 * (d : ℝ) * (ρ ^ α) ^ 2 := by
    have hZ0 : 0 ≤ Hα * (Real.sqrt d) ^ (α - β) * ρ ^ α :=
      mul_nonneg (mul_nonneg hHα0 hpow0) hρα.le
    have hsq := pow_le_pow_left₀ hY0 hY 2
    have hHd : Hα * (Real.sqrt d) ^ (α - β) ≤ (Kg * g) * Real.sqrt d :=
      mul_le_mul hHα hpow1 hpow0 (hHα0.trans hHα)
    have hHd0 : 0 ≤ Hα * (Real.sqrt d) ^ (α - β) := mul_nonneg hHα0 hpow0
    have hsq2 := pow_le_pow_left₀ hHd0 hHd 2
    have hsqd : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
    calc (ρ ^ β * X) ^ 2 ≤ (Hα * (Real.sqrt d) ^ (α - β) * ρ ^ α) ^ 2 := hsq
      _ = (Hα * (Real.sqrt d) ^ (α - β)) ^ 2 * (ρ ^ α) ^ 2 := by ring
      _ ≤ ((Kg * g) * Real.sqrt d) ^ 2 * (ρ ^ α) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq2 (sq_nonneg _)
      _ = (Kg * g) ^ 2 * (Real.sqrt d) ^ 2 * (ρ ^ α) ^ 2 := by ring
      _ = (Kg * g) ^ 2 * (d : ℝ) * (ρ ^ α) ^ 2 := by rw [hsqd]
  -- the power of `ρ`
  have hρd : 0 < ρ ^ ((d : ℝ) - 2) := Real.rpow_pos_of_pos hρ _
  have hexp : ρ ^ (-η) * ρ ^ ((d : ℝ) - 2) * (ρ ^ α) ^ 2 ≤ ρ ^ ((d : ℝ) - σ) := by
    have heq : ρ ^ (-η) * ρ ^ ((d : ℝ) - 2) * (ρ ^ α) ^ 2 =
        ρ ^ (-η + ((d : ℝ) - 2) + 2 * α) := by
      rw [sq, ← Real.rpow_add hρ, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
      congr 1
      ring
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have hKe0 : 0 ≤ Ke * ρ ^ (-η) := hLam0.trans hLam
  calc C1 * Lam * ρ ^ ((d : ℝ) - 2) * (ρ ^ β * X) ^ 2
      ≤ C1 * (Ke * ρ ^ (-η)) * ρ ^ ((d : ℝ) - 2) *
          ((Kg * g) ^ 2 * (d : ℝ) * (ρ ^ α) ^ 2) := by
        apply mul_le_mul _ hY2 (sq_nonneg _)
        · exact mul_nonneg (mul_nonneg hC1 hKe0) hρd.le
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLam hC1) hρd.le
    _ = C1 * (d : ℝ) * Ke * Kg ^ 2 * g ^ 2 *
          (ρ ^ (-η) * ρ ^ ((d : ℝ) - 2) * (ρ ^ α) ^ 2) := by ring
    _ ≤ C1 * (d : ℝ) * Ke * Kg ^ 2 * g ^ 2 * ρ ^ ((d : ℝ) - σ) := by
        apply mul_le_mul_of_nonneg_left hexp
        have hKe : 0 ≤ Ke := by
          by_contra hneg
          push Not at hneg
          have := mul_neg_of_neg_of_pos hneg (Real.rpow_pos_of_pos hρ (-η))
          linarith
        have : 0 ≤ C1 * (d : ℝ) * Ke := mul_nonneg (mul_nonneg hC1 (Nat.cast_nonneg d)) hKe
        positivity
    _ = C1 * (d : ℝ) * Ke * Kg ^ 2 * ρ ^ ((d : ℝ) - σ) * g ^ 2 := by ring


variable {d : ℕ}

/-- The unit root `openCubeSet (originCube d 0)` is `(-1/2, 1/2)^d`. -/
theorem aux_lem_finite_stopping_crude_cost_mem_unit_root {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) (i : Fin d) :
    -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
  have h : ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
    simpa [Homogenization.openCubeSet, Homogenization.originCube,
      Homogenization.cubeScaleFactor] using hx
  exact h i

/-- The chart `x ↦ w + r x` maps the unit root into `centeredCube w r`. -/
theorem aux_lem_finite_stopping_crude_cost_affine_mem (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    (fun i => w i + r * x i) ∈ (centeredCube w r hr : Set (SpatialCoordinates d)) := by
  rw [centeredCube_eq_pi]
  intro i _
  obtain ⟨h1, h2⟩ := aux_lem_finite_stopping_crude_cost_mem_unit_root hx i
  have h1' : r * (-(1 / 2 : ℝ)) < r * x i := mul_lt_mul_of_pos_left h1 hr
  have h2' : r * x i < r * (1 / 2 : ℝ) := mul_lt_mul_of_pos_left h2 hr
  constructor <;> linarith

/-- The affine chart is quasi-measure-preserving for Lebesgue measure. -/
theorem aux_lem_finite_stopping_crude_cost_qmp_affine (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => fun i => w i + r * x i)
      volume volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => r • y)
      volume volume :=
    Measure.quasiMeasurePreserving_smul volume hr.ne'
  have h2 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => y + w)
      volume volume :=
    (measurePreserving_add_right volume w).quasiMeasurePreserving
  have heq : (fun x : SpatialCoordinates d => fun i => w i + r * x i) =
      (fun y : SpatialCoordinates d => y + w) ∘ (fun y : SpatialCoordinates d => r • y) := by
    funext x i
    simp [add_comm]
  rw [heq]
  exact h2.comp h1

/-- A.e. statements on a set pull back along a quasi-measure-preserving map sending a
second set into the first. -/
theorem aux_lem_finite_stopping_crude_cost_ae_restrict_comp {f : SpatialCoordinates d → SpatialCoordinates d}
    (hf : Measure.QuasiMeasurePreserving f volume volume) {S S' : Set (SpatialCoordinates d)}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hmaps : ∀ y ∈ S', f y ∈ S)
    {P : SpatialCoordinates d → Prop} (h : ∀ᵐ x ∂volume.restrict S, P x) :
    ∀ᵐ y ∂volume.restrict S', P (f y) := by
  rw [ae_restrict_iff' hS] at h
  rw [ae_restrict_iff' hS']
  filter_upwards [hf.ae h] with y hy hyS'
  exact hy (hmaps y hyS')

/-- **Rechart.**  The multiscale carrier `Λ` of a subcube, computed with the literal
restricted coefficient on the subcube's own chart, equals the root carrier read on
the same chart. -/
theorem aux_lem_finite_stopping_crude_cost_Lam_restrict_eq (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) {z : SpatialCoordinates d} {R : ℝ}
    (hR : 0 < R) (a : PositiveCoefficient (centeredCube z R hR))
    {w : SpatialCoordinates d} {r' : ℝ} (hr' : 0 < r')
    (hle : centeredCube w r' hr' ≤ centeredCube z R hR)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (q : ENNReal) (hq : 1 ≤ q) :
    Jc.Lam w r' hr' (positiveCoefficientRestrict hle a) w r' s q =
      Jc.Lam z R hR a w r' s q := by
  rw [Jc.Lam_eq w r' hr' _ w r' hr' subset_rfl s hs q hq,
    Jc.Lam_eq z R hR a w r' hr' hle s hs q hq]
  apply SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.LambdaSq_eq_of_descendantAEEq
  intro k S hS
  by_cases hk : k ≤ (Homogenization.originCube d 0).scale
  · have hsub := Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk hS
    have h1 := Jc.chart_eq w r' hr' (positiveCoefficientRestrict hle a) w r' hr' subset_rfl S hsub
    have h2 := Jc.chart_eq z R hR a w r' hr' hle S hsub
    have hmaps : ∀ x ∈ Homogenization.openCubeSet S,
        (fun i => w i + r' * x i) ∈ (centeredCube w r' hr' : Set (SpatialCoordinates d)) :=
      fun x hx => aux_lem_finite_stopping_crude_cost_affine_mem w r' hr' (hsub hx)
    have h3 := aux_lem_finite_stopping_crude_cost_ae_restrict_comp (aux_lem_finite_stopping_crude_cost_qmp_affine w r' hr')
      (centeredCube w r' hr').isOpen.measurableSet
      (Homogenization.measurableSet_openCubeSet S) hmaps
      (positiveCoefficientRestrict_coeFn hle a)
    show _ =ᵐ[volume.restrict (Homogenization.openCubeSet S)] _
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hx1, hx2]
    exact congrArg _ hx3
  · exfalso
    simp [Homogenization.descendantsAtScale, hk] at hS


variable {d : ℕ}

/-- Descendant centres lie on the grid of their own side. -/
theorem aux_lem_finite_stopping_crude_cost_descendantCenter_grid (m : ℕ) (z : SpatialCoordinates d) (r : ℝ) :
    ∀ (n : ℕ) (w : Fin n → OddGridIndex d m), ∃ a : Fin d → ℤ,
      descendantCenter m z r n w = fun i => z i + descendantSide m n r * (a i : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro w
    refine ⟨0, ?_⟩
    funext i
    show z i = z i + descendantSide m 0 r * (((0 : Fin d → ℤ) i : ℤ) : ℝ)
    simp
  | succ n ih =>
    intro w
    obtain ⟨a, ha⟩ := ih (fun i => w i.castSucc)
    refine ⟨fun i => (2 * (m : ℤ) + 1) * a i + (((w (Fin.last n) i : ℕ) : ℤ) - m), ?_⟩
    funext i
    have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
    change oddGridCenter (descendantCenter m z r n fun i => w i.castSucc)
        (descendantSide m n r) m (w (Fin.last n)) i = _
    unfold oddGridCenter
    rw [ha, descendantSide_succ]
    push_cast
    field_simp
    ring

/-- Stage-2 centres lie on the grid of the stage-2 side, based at the root centre. -/
theorem aux_lem_finite_stopping_crude_cost_cell2_center_grid (z : SpatialCoordinates d) (r : ℝ) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    ∃ a : Fin d → ℤ,
      descendantCenter mg (descendantCenter 1 z r t0 w0) (descendantSide 1 t0 r) s w =
        fun i => z i + descendantSide mg s (descendantSide 1 t0 r) * (a i : ℝ) := by
  obtain ⟨a0, ha0⟩ := aux_lem_finite_stopping_crude_cost_descendantCenter_grid 1 z r t0 w0
  obtain ⟨b, hb⟩ := aux_lem_finite_stopping_crude_cost_descendantCenter_grid mg (descendantCenter 1 z r t0 w0)
    (descendantSide 1 t0 r) s w
  refine ⟨fun i => (2 * (mg : ℤ) + 1) ^ s * a0 i + b i, ?_⟩
  rw [hb, ha0]
  funext i
  have hpos : (0 : ℝ) < 2 * (mg : ℝ) + 1 := by positivity
  have hside : descendantSide 1 t0 r =
      descendantSide mg s (descendantSide 1 t0 r) * (2 * (mg : ℝ) + 1) ^ s := by
    unfold descendantSide
    field_simp
  simp only
  generalize descendantSide mg s (descendantSide 1 t0 r) = S2 at hside ⊢
  rw [hside]
  push_cast
  ring

/-- Congruence of centred cubes. -/
theorem aux_lem_finite_stopping_crude_cost_centeredCube_congr {c c' : SpatialCoordinates d} {ρ ρ' : ℝ} (hc : c = c')
    (hρ : ρ = ρ') (h : 0 < ρ) (h' : 0 < ρ') : centeredCube c ρ h = centeredCube c' ρ' h' := by
  subst hc
  subst hρ
  rfl

/-- **Final-cell grid form.**  For `N ≥ 4|j|`, every stage-2 cell at depth `s` of the
two-stage tree of `centeredCube z 3^j` is the grid cube
`centeredCube (z + 3^(-k) a) 3^(-k)` with `k = H1 (aux_lem_finite_stopping_crude_cost_obsLo + s)`. -/
theorem aux_lem_finite_stopping_crude_cost_cell2_grid {H1 : ℕ} (hH1 : 0 < H1) {N : ℕ} {j : ℤ} (hN : 4 * j.natAbs ≤ N)
    (z : SpatialCoordinates d) (w0 : Fin (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d (subdivisionHalfWidth H1)) :
    ∃ a : Fin d → ℤ,
      descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) w0)
          (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j)) s w =
        (fun i => z i + (3 : ℝ) ^ (-((H1 * (aux_lem_finite_stopping_crude_cost_obsLo H1 N + s) : ℕ) : ℤ)) * (a i : ℝ)) ∧
      descendantSide (subdivisionHalfWidth H1) s
          (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j)) =
        (3 : ℝ) ^ (-((H1 * (aux_lem_finite_stopping_crude_cost_obsLo H1 N + s) : ℕ) : ℤ)) := by
  obtain ⟨a, ha⟩ := aux_lem_finite_stopping_crude_cost_cell2_center_grid z ((3 : ℝ) ^ j) (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j)
    (subdivisionHalfWidth H1) w0 s w
  have hside := aux_lem_finite_stopping_crude_cost_stage_side_eq hH1 hN s
  refine ⟨a, ?_, hside⟩
  rw [ha, hside]


variable {d : ℕ}

/-! ## Literal supplier bodies -/

/-- The one-sample body of `prop_growth` at the root `centeredCube z r hr`
(`K` is the sample value `N ↦ K N om`). -/
def aux_lem_finite_stopping_crude_cost_GrowthAt [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t alpha : ℝ)
    (om : BilateralField d) (K : ℕ → ℝ) : Prop :=
  ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf →
    AEMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
    (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      |F x| ≤ Kf) →
  ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
    ContDiff ℝ 2 phi →
    c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
  ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
    ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
    SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
    (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
      0 < rad → rad ≤ 1 →
      localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter
            (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        K N * (Kf + Cphi) ^ 2 * rad ^ t) ∧
    (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        K N * (Kf + Cphi))

/-- The full conclusion of `prop_growth` at one root, for the moment list `ps`. -/
def aux_lem_finite_stopping_crude_cost_GrowthBody [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ) : Prop :=
  (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
  (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
    ENNReal.ofReal (Cbound i)) ∧
  (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
  ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, aux_lem_finite_stopping_crude_cost_GrowthAt M H z r hr t alpha om (fun N => K N om)

/-- Clause 1 of `lem_extension` (paper eq. `mfd-2`) with its constant `C`. -/
def aux_lem_finite_stopping_crude_cost_ClauseOne (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (beta C : ℝ) : Prop :=
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (a : PositiveCoefficient (centeredCube z r hr))
      (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      dirichletResponse (killedResponseSpace hP) a b ≤
        C * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
          (r ^ beta *
            holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2

/-- Clause 2 of `lem_extension` (paper eq. `mfd-3`) at one sample, for the grid
family `{z + 3^(-k) ℤ^d}` of the root `centeredCube z 3^j` (`K N` is the sample value). -/
def aux_lem_finite_stopping_crude_cost_ClauseTwoAt [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d) (j : ℤ)
    (beta eta : ℝ) (om : BilateralField d) (K : ℕ → ℝ) : Prop :=
  ∀ (N k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
    (centeredCube (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
        ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
      centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)) →
    Jc.Lam z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)
        (cutoffPositiveCoefficient M H om N z (zpow_pos (by norm_num) j))
        (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ)))
        ((beta - 1 / 2) / 4) 2 +
      (Jc.lam z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)
        (cutoffPositiveCoefficient M H om N z (zpow_pos (by norm_num) j))
        (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ)))
        ((beta - 1 / 2) / 4) 2)⁻¹ ≤
      K N * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta)

/-! ## Energy identities -/



theorem aux_lem_finite_stopping_crude_cost_energyOn_eq_local {Q : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Q)
    (u : SobolevData Q) {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (hsQ : s ⊆ Q) :
    aux_lem_finite_stopping_crude_cost_energyOn a u s = localGradientEnergy a hs (sobolevGradient u) := by
  rw [localGradientEnergy_eq_integral]
  unfold aux_lem_finite_stopping_crude_cost_energyOn
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.restrict_restrict hs, Set.inter_eq_left.2 hsQ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [sq]
  rfl

/-- The minimizer solves the zero-source Dirichlet problem. -/
theorem aux_lem_finite_stopping_crude_cost_minimizer_solves_zero {Q : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖)
    (a : PositiveCoefficient Q) (b : weakSobolevGraph Q) :
    SolvesDirichlet a (fun _ => (0 : ℝ)) b
      (@dirichletMinimizer d Q (@killedResponseSpace d Q hP) a b) := by
  refine ⟨dirichletMinimizer_mem_affine (killedResponseSpace hP) a b, fun ψ => ?_⟩
  have h := dirichletMinimizer_euler (killedResponseSpace hP) a b ψ
  simp only [zero_mul, integral_zero]
  exact h

/-- Same-depth descendant cells are pairwise disjoint. -/
theorem aux_lem_finite_stopping_crude_cost_descendantCells_pairwise (m : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) :
    Pairwise (fun w w' : Fin n → OddGridIndex d m =>
      Disjoint (descendantCell m z hr n w : Set (SpatialCoordinates d))
        (descendantCell m z hr n w' : Set (SpatialCoordinates d))) := by
  intro w w' hne
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hne (aux_lem_finite_stopping_crude_cost_descendantCell_word_eq_of_mem m z hr n w w' x hx hx')

/-- Covering: if every unit ball around a point of the root carries energy `≤ X`, the
root energy is at most `3^(d n) X`, `n` a depth at which triadic cells have side `≤ 1`. -/
theorem aux_lem_finite_stopping_crude_cost_energy_cover (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R) (n : ℕ)
    (hside : descendantSide 1 n R ≤ 1) (a : PositiveCoefficient (centeredCube z R hR))
    (u : SobolevData (centeredCube z R hR)) (X : ℝ)
    (hX : ∀ c ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      aux_lem_finite_stopping_crude_cost_energyOn a u (Metric.ball c 1 ∩ (centeredCube z R hR : Set (SpatialCoordinates d))) ≤ X) :
    aux_lem_finite_stopping_crude_cost_energyOn a u (centeredCube z R hR : Set (SpatialCoordinates d)) ≤ ((3 : ℝ) ^ d) ^ n * X := by
  have hcov := aux_lem_finite_stopping_crude_cost_descendantCells_union_ae_eq 1 z hR n
  rw [← aux_lem_finite_stopping_crude_cost_energyOn_sum_eq a u (fun w => (descendantCell 1 z hR n w : Set (SpatialCoordinates d)))
    (fun w => (descendantCell 1 z hR n w).isOpen.measurableSet)
    (fun w => aux_lem_finite_stopping_crude_cost_descendantCell_subset_root 1 z hR n w)
    (aux_lem_finite_stopping_crude_cost_descendantCells_pairwise 1 z hR n) hcov]
  have hcell : ∀ w : Fin n → OddGridIndex d 1,
      aux_lem_finite_stopping_crude_cost_energyOn a u (descendantCell 1 z hR n w : Set (SpatialCoordinates d)) ≤ X := by
    intro w
    have hpos := descendantSide_pos 1 n hR
    have hcQ : descendantCenter 1 z R n w ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) :=
      aux_lem_finite_stopping_crude_cost_descendantCell_subset_root 1 z hR n w (Metric.mem_ball_self (half_pos hpos))
    have hsub : (descendantCell 1 z hR n w : Set (SpatialCoordinates d)) ⊆
        Metric.ball (descendantCenter 1 z R n w) 1 ∩
          (centeredCube z R hR : Set (SpatialCoordinates d)) := by
      intro x hx
      refine ⟨Metric.ball_subset_ball (by linarith) hx,
        aux_lem_finite_stopping_crude_cost_descendantCell_subset_root 1 z hR n w hx⟩
    exact (aux_lem_finite_stopping_crude_cost_energyOn_mono a u hsub Set.inter_subset_right).trans (hX _ hcQ)
  have hcard : (Fintype.card (Fin n → OddGridIndex d 1) : ℝ) = ((3 : ℝ) ^ d) ^ n := by
    simp [Fintype.card_fin]
  calc (∑ w : Fin n → OddGridIndex d 1,
        aux_lem_finite_stopping_crude_cost_energyOn a u (descendantCell 1 z hR n w : Set (SpatialCoordinates d)))
      ≤ ∑ _w : Fin n → OddGridIndex d 1, X := Finset.sum_le_sum fun w _ => hcell w
    _ = ((3 : ℝ) ^ d) ^ n * X := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]

/-- The depth `j⁺` triadic cells of a cube of side `3^j` have side `≤ 1`. -/
theorem aux_lem_finite_stopping_crude_cost_side_toNat_le_one (j : ℤ) : descendantSide 1 j.toNat ((3 : ℝ) ^ j) ≤ 1 := by
  rw [aux_lem_finite_stopping_crude_cost_descendantSide_zpow 1 1 (by norm_num) j j.toNat]
  apply zpow_le_one_of_nonpos₀ (by norm_num)
  have : j ≤ (j.toNat : ℤ) := Int.self_le_toNat j
  push_cast
  omega

/-- **Global energy** : with the local energy clause of `prop_growth`
at the root, the source response is at most `3^(d n) K_N ‖g‖²_{C²}`. -/
theorem aux_lem_finite_stopping_crude_cost_root_energy [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {z : SpatialCoordinates d} {R : ℝ} {hR : 0 < R} {t alpha : ℝ} {om : BilateralField d}
    {K : ℕ → ℝ} (hG : aux_lem_finite_stopping_crude_cost_GrowthAt M H z R hR t alpha om K) (n : ℕ)
    (hside : descendantSide 1 n R ≤ 1) (N : ℕ)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z R hR),
      ‖(v : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z R hR) (killedSobolevGraph (centeredCube z R hR)) v‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi)
    (b : weakSobolevGraph (centeredCube z R hR))
    (hb : ((b : SobolevData (centeredCube z R hR)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] phi) :
    @dirichletResponse d _ (@killedResponseSpace d _ hP)
        (cutoffPositiveCoefficient M H om N z hR) b ≤
      ((3 : ℝ) ^ d) ^ n * K N *
        (c2Norm (closedCube z R hR : Set (SpatialCoordinates d)) phi) ^ 2 := by
  have hsol := aux_lem_finite_stopping_crude_cost_minimizer_solves_zero hP (cutoffPositiveCoefficient M H om N z hR) b
  have hG1 := hG N (fun _ => (0 : ℝ)) 0 le_rfl aemeasurable_const
    (Eventually.of_forall fun x => by simp) phi
    (c2Norm (closedCube z R hR : Set (SpatialCoordinates d)) phi) hphi le_rfl b _ hb hsol
  have hloc := hG1.1
  rw [aux_lem_finite_stopping_crude_cost_dirichletResponse_eq_energyOn, mul_assoc]
  refine aux_lem_finite_stopping_crude_cost_energy_cover z hR n hside _ _ _ fun c hc => ?_
  have hmeas : MeasurableSet (Metric.ball c 1 ∩ (centeredCube z R hR : Set (SpatialCoordinates d))) :=
    Metric.isOpen_ball.measurableSet.inter (centeredCube z R hR).isOpen.measurableSet
  rw [aux_lem_finite_stopping_crude_cost_energyOn_eq_local _ _ hmeas Set.inter_subset_right]
  refine (hloc c 1 hc one_pos le_rfl).trans (le_of_eq ?_)
  rw [Real.one_rpow, zero_add, mul_one]

/-- **Crude cell cost** : clause 1 of `lem_extension` on a subcube of
side `ρ ≤ 1`, the rechart to the root grid carrier, and the `C^α` bound. -/
theorem aux_lem_finite_stopping_crude_cost_cell_cost (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) {β α η σ C1 : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hβα : β ≤ α) (hαβ1 : α - β ≤ 1) (hσ : 2 - 2 * α + η ≤ σ) (hd : 1 ≤ d)
    (hC1 : 0 < C1) (h1 : aux_lem_finite_stopping_crude_cost_ClauseOne Jc β C1)
    {z : SpatialCoordinates d} {R : ℝ} (hR : 0 < R) {c : SpatialCoordinates d} {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hle : centeredCube c ρ hρ ≤ centeredCube z R hR)
    (hPq : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube c ρ hρ),
      ‖(v : SobolevData (centeredCube c ρ hρ)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube c ρ hρ)) v‖)
    (aT : PositiveCoefficient (centeredCube z R hR))
    (u : weakSobolevGraph (centeredCube z R hR))
    (U : SpatialCoordinates d → ℝ) (hUc : Continuous U)
    (hUu : ((u : SobolevData (centeredCube z R hR)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] U)
    (hUh : IsHolderOn α (closedCube z R hR : Set (SpatialCoordinates d)) U) {Kg g : ℝ}
    (hUn : cAlphaNorm α (closedCube z R hR : Set (SpatialCoordinates d)) U ≤ Kg * g)
    {Ke : ℝ} (hLam : Jc.Lam z R hR aT c ρ ((β - 1 / 2) / 4) 2 ≤ Ke * ρ ^ (-η)) :
    aux_lem_finite_stopping_crude_cost_respOn aT u hle hPq ≤ C1 * (d : ℝ) * Ke * Kg ^ 2 * ρ ^ ((d : ℝ) - σ) * g ^ 2 := by
  have hs : (β - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  have hrech := aux_lem_finite_stopping_crude_cost_Lam_restrict_eq Jc hR aT hρ hle _ hs 2 (by norm_num)
  have hb : (((⟨sobolevDataRestrict hle u.val, sobolevDataRestrict_mem_weak hle u.property⟩ :
      weakSobolevGraph (centeredCube c ρ hρ)) : SobolevData (centeredCube c ρ hρ)).1 :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube c ρ hρ : Set (SpatialCoordinates d))] U := by
    have e1 := domainLpRestrict_coeFn hle (u.val.1)
    have e2 := ae_restrict_of_ae_restrict_of_subset
      (show (centeredCube c ρ hρ : Set (SpatialCoordinates d)) ⊆ centeredCube z R hR from hle) hUu
    filter_upwards [e1, e2] with x hx1 hx2
    exact hx1.trans hx2
  have hfront := aux_lem_finite_stopping_crude_cost_frontier_subset_closedCube hR hρ hle
  obtain ⟨hHβ, hsemi⟩ := aux_lem_finite_stopping_crude_cost_holder_downgrade hβα
    (mul_nonneg (Real.sqrt_nonneg _) hρ.le) hfront U hUh (aux_lem_finite_stopping_crude_cost_frontier_euclid_le hρ)
  have hresp := h1 c ρ hρ hρ1 hPq (positiveCoefficientRestrict hle aT) U
    ⟨sobolevDataRestrict hle u.val, sobolevDataRestrict_mem_weak hle u.property⟩
    hUc.continuousOn hHβ hb
  rw [hrech] at hresp
  unfold aux_lem_finite_stopping_crude_cost_respOn
  refine hresp.trans ?_
  exact aux_lem_finite_stopping_crude_cost_crude_real hd hC1.le (Jc.Lam_pos _ _ _ _ _ _ _ _).le hLam
    (aux_lem_finite_stopping_crude_cost_holderSeminorm_nonneg _ _ _) hsemi (aux_lem_finite_stopping_crude_cost_holderSeminorm_nonneg _ _ _)
    ((aux_lem_finite_stopping_crude_cost_holderSeminorm_le_cAlphaNorm _ _ _).trans hUn) hρ hρ1 hαβ1 hσ


variable {d : ℕ}

/-- The body of the ChildB proposition after the root and the tree scale. -/
def aux_lem_finite_stopping_crude_cost_ChildBRootBody (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (σ : ℝ)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ) : Prop :=
  haveI : NeZero d := ⟨by omega⟩
  ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
  ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
  ∀ hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
      (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
    ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))).1‖ ≤
      K * ‖@subspaceGradient d (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))
        (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))) v‖,
  ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
  ∀ b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
    ((b : SobolevData (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))).1 :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) :
          Set (SpatialCoordinates d))] phi →
  ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
    (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
    ∀ omega ∉ Bad,
    let hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
    let target := if reverse then M else N
    let source := if reverse then N else M
    let aT := cutoffPositiveCoefficient model H omega target z hr
    let aS := cutoffPositiveCoefficient model H omega source z hr
    let u := @dirichletMinimizer d _ (@killedResponseSpace d _ hP) aS b
    let mg := subdivisionHalfWidth H1
    let t0 := aux_lem_finite_stopping_crude_cost_obsT0 H1 N j
    let B := aux_lem_finite_stopping_crude_cost_obsB H1 N
    let gnorm : ℝ := c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi
    (∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
      aux_lem_finite_stopping_crude_cost_respOn aT u (aux_lem_finite_stopping_crude_cost_cell2_le_root z hr t0 mg w0 B w)
          (aux_lem_finite_stopping_crude_cost_cell2_killedPoincare z hr t0 mg w0 B w) ≤
        (3 : ℝ) ^ (ε * (N : ℝ)) *
          (descendantSide mg B (descendantSide 1 t0 ((3 : ℝ) ^ j))) ^ ((d : ℝ) - σ) *
            (gnorm * gnorm)) ∧
    @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b ≤
      (3 : ℝ) ^ (ε * (N : ℝ)) * (gnorm * gnorm)

/-- **Refined child B with the stated standing inputs** (all triadic roots). -/
def aux_lem_finite_stopping_crude_cost_ChildBIn (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) : Prop :=
  ∀ σ : ℝ, 0 < σ → ∃ delta0 : ℝ, 0 < delta0 ∧
  ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
    (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
    InfraredCharacterization model H → model.delta ≤ delta0 →
  ∀ (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ), 0 < H1 →
    aux_lem_finite_stopping_crude_cost_ChildBRootBody d hd σ model H z j H1

/-- **Refined child B with the stated standing inputs**, roots of side `3^j ≤ 1`. -/
def aux_lem_finite_stopping_crude_cost_ChildBInLe (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) : Prop :=
  ∀ σ : ℝ, 0 < σ → ∃ delta0 : ℝ, 0 < delta0 ∧
  ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
    (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
    InfraredCharacterization model H → model.delta ≤ delta0 →
  ∀ (z : SpatialCoordinates d) (j : ℤ), j ≤ 0 → ∀ (H1 : ℕ), 0 < H1 →
    aux_lem_finite_stopping_crude_cost_ChildBRootBody d hd σ model H z j H1

/-- **The exact missing supplier for roots of side `> 1`**: `prop_growth` with its side
restriction `r ≤ 1` replaced by `1 < r` (everything else verbatim). -/
def aux_lem_finite_stopping_crude_cost_LargeRootGrowth (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) : Prop :=
  ∀ (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
      (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), 1 < r →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        aux_lem_finite_stopping_crude_cost_GrowthBody M H z r hr t alpha k ps K Cbound

/-- `aux_lem_finite_stopping_crude_cost_GrowthBody` is literally the conclusion of `prop_growth` at a root of side `≤ 1`. -/
theorem aux_lem_finite_stopping_crude_cost_growthBody_of_prop_growth (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (h1 : (d : ℝ) - 1 < t) (h2 : t < d) (h3 : 0 < alpha) (h4 : alpha < 1)
    (h5 : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
      (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        aux_lem_finite_stopping_crude_cost_GrowthBody M H z r hr t alpha k ps K Cbound :=
  _root_.SubdiffusiveProcess.Paper.prop_growth d hd Jc Pc Xc W Cp Sf t alpha k ps h1 h2 h3 h4 h5

/-! ## One sample -/

/-- Both ChildB clauses at one sample, with the explicit random constants. -/
theorem aux_lem_finite_stopping_crude_cost_omega_final (hd : 2 ≤ d) [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    {σ α β η t C1 : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) (hβα : β ≤ α) (hαβ1 : α - β ≤ 1)
    (hσ : 2 - 2 * α + η ≤ σ) (hC1 : 0 < C1) (h1 : aux_lem_finite_stopping_crude_cost_ClauseOne Jc β C1)
    {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (z : SpatialCoordinates d) (j : ℤ) (hr : (0 : ℝ) < (3 : ℝ) ^ j) (H1 : ℕ) (hH1 : 0 < H1)
    (N : ℕ) (hNj : 4 * j.natAbs ≤ N) (hNH : 4 * H1 ≤ N) (T S : ℕ) (hNT : N ≤ T)
    (omega : BilateralField d) (Kg Ke : ℕ → ℝ)
    (hGω : aux_lem_finite_stopping_crude_cost_GrowthAt model H z ((3 : ℝ) ^ j) hr t α omega Kg)
    (hEω : aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η omega Ke)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
        (centeredCube z ((3 : ℝ) ^ j) hr),
      ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z ((3 : ℝ) ^ j) hr)
          (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr)) v‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (hb : ((b : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ j) hr :
          Set (SpatialCoordinates d))] phi) :
    (∀ (w0 : Fin (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) → OddGridIndex d 1)
        (w : Fin (aux_lem_finite_stopping_crude_cost_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      aux_lem_finite_stopping_crude_cost_respOn (cutoffPositiveCoefficient model H omega T z hr)
          (@dirichletMinimizer d (centeredCube z ((3 : ℝ) ^ j) hr)
            (@killedResponseSpace d (centeredCube z ((3 : ℝ) ^ j) hr) hP)
            (cutoffPositiveCoefficient model H omega S z hr) b)
          (aux_lem_finite_stopping_crude_cost_cell2_le_root z hr (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j)
            (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
          (aux_lem_finite_stopping_crude_cost_cell2_killedPoincare z hr (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j)
            (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_crude_cost_obsB H1 N) w) ≤
        (C1 * (d : ℝ) * |Ke T| * |Kg S| ^ 2) *
          (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_crude_cost_obsB H1 N)
            (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - σ) *
            (c2Norm (closedCube z ((3 : ℝ) ^ j) hr :
              Set (SpatialCoordinates d)) phi *
            c2Norm (closedCube z ((3 : ℝ) ^ j) hr :
              Set (SpatialCoordinates d)) phi)) ∧
    @dirichletResponse d (centeredCube z ((3 : ℝ) ^ j) hr)
        (@killedResponseSpace d (centeredCube z ((3 : ℝ) ^ j) hr) hP)
        (cutoffPositiveCoefficient model H omega S z hr) b ≤
      (((3 : ℝ) ^ d) ^ j.toNat * |Kg S|) *
        (c2Norm (closedCube z ((3 : ℝ) ^ j) hr :
            Set (SpatialCoordinates d)) phi *
          c2Norm (closedCube z ((3 : ℝ) ^ j) hr :
            Set (SpatialCoordinates d)) phi) := by
  have hphi2 : ContDiff ℝ 2 phi :=
    hphi.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hg0 : 0 ≤ c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi :=
    aux_lem_finite_stopping_crude_cost_c2Norm_nonneg _ _
  constructor
  · -- crude cost of every final observation cell
    have hsol := aux_lem_finite_stopping_crude_cost_minimizer_solves_zero hP
      (cutoffPositiveCoefficient model H omega S z hr) b
    have hG1 := hGω S (fun _ => (0 : ℝ)) 0 le_rfl aemeasurable_const
      (Eventually.of_forall fun x => by simp) phi
      (c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) hphi2 le_rfl
      b _ hb hsol
    obtain ⟨U, hUc, hUu, hUh, hUn⟩ := hG1.2
    have hUn' : cAlphaNorm α (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) U ≤
        |Kg S| * c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi := by
      refine hUn.trans ?_
      rw [zero_add]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hg0
    intro w0 w
    obtain ⟨a, hc, hside⟩ := aux_lem_finite_stopping_crude_cost_cell2_grid hH1 hNj z w0 (aux_lem_finite_stopping_crude_cost_obsB H1 N) w
    have hkT : H1 * (aux_lem_finite_stopping_crude_cost_obsLo H1 N + aux_lem_finite_stopping_crude_cost_obsB H1 N) ≤ T := by
      have hlh := aux_lem_finite_stopping_crude_cost_obsLo_le_obsHi hH1 hNH
      have hsum : aux_lem_finite_stopping_crude_cost_obsLo H1 N + aux_lem_finite_stopping_crude_cost_obsB H1 N = aux_lem_finite_stopping_crude_cost_obsHi H1 N := by
        unfold aux_lem_finite_stopping_crude_cost_obsB; omega
      have h4 := aux_lem_finite_stopping_crude_cost_four_H1_obsHi_le hH1 N
      rw [hsum]
      omega
    have hpos := descendantSide_pos (subdivisionHalfWidth H1) (aux_lem_finite_stopping_crude_cost_obsB H1 N)
      (descendantSide_pos 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) hr)
    have hsub : centeredCube
        (fun i => z i + (3 : ℝ) ^ (-((H1 * (aux_lem_finite_stopping_crude_cost_obsLo H1 N + aux_lem_finite_stopping_crude_cost_obsB H1 N) : ℕ) : ℤ)) * (a i : ℝ))
        ((3 : ℝ) ^ (-((H1 * (aux_lem_finite_stopping_crude_cost_obsLo H1 N + aux_lem_finite_stopping_crude_cost_obsB H1 N) : ℕ) : ℤ))) (by positivity) ≤
        centeredCube z ((3 : ℝ) ^ j) hr :=
      (le_of_eq (aux_lem_finite_stopping_crude_cost_centeredCube_congr hc hside hpos (by positivity)).symm).trans
        (aux_lem_finite_stopping_crude_cost_cell2_le_root z hr (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
          (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
    have hE := hEω T _ a hkT hsub
    rw [← hc, ← hside] at hE
    have hLam : Jc.Lam z ((3 : ℝ) ^ j) hr
        (cutoffPositiveCoefficient model H omega T z hr)
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) w0)
          (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j)) (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
        (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_crude_cost_obsB H1 N)
          (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j)))
        ((β - 1 / 2) / 4) 2 ≤
        |Ke T| * (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_crude_cost_obsB H1 N)
          (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ (-η) := by
      refine le_trans (le_add_of_nonneg_right (inv_nonneg.2 (Jc.lam_pos _ _ _ _ _ _ _ _).le))
        (hE.trans ?_)
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hpos.le _)
    have hρ1 : descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_crude_cost_obsB H1 N)
        (descendantSide 1 (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) ((3 : ℝ) ^ j)) ≤ 1 := by
      rw [hside]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hcost := aux_lem_finite_stopping_crude_cost_cell_cost Jc hβ hβα hαβ1 hσ (by omega) hC1 h1 hr hpos hρ1
      (aux_lem_finite_stopping_crude_cost_cell2_le_root z hr (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
      (aux_lem_finite_stopping_crude_cost_cell2_killedPoincare z hr (aux_lem_finite_stopping_crude_cost_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
        (aux_lem_finite_stopping_crude_cost_obsB H1 N) w)
      (cutoffPositiveCoefficient model H omega T z hr) _ U hUc hUu hUh hUn' hLam
    refine hcost.trans (le_of_eq ?_)
    ring
  · -- global source energy
    have h := aux_lem_finite_stopping_crude_cost_root_energy hGω j.toNat (aux_lem_finite_stopping_crude_cost_side_toNat_le_one j) S hP phi hphi2 b hb
    refine h.trans ?_
    have h3 : 0 ≤ ((3 : ℝ) ^ d) ^ j.toNat := by positivity
    calc ((3 : ℝ) ^ d) ^ j.toNat * Kg S *
          c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi ^ 2
        ≤ ((3 : ℝ) ^ d) ^ j.toNat * |Kg S| *
          c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left (le_abs_self _) h3
      _ = _ := by ring


variable {d : ℕ}

/-- An exponential beats a fixed constant. -/
theorem aux_lem_finite_stopping_crude_cost_exists_nat_const_le_rpow (X ε : ℝ) (hε : 0 < ε) :
    ∃ N1 : ℕ, X ≤ (3 : ℝ) ^ (ε * (N1 : ℝ)) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt X
    (show (1 : ℝ) < (3 : ℝ) ^ ε from Real.one_lt_rpow (by norm_num) hε)
  refine ⟨n, hn.le.trans (le_of_eq ?_)⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

/-- Four factors bounded by `3^(εN/4)` give `3^(εN)`. -/
theorem aux_lem_finite_stopping_crude_cost_four_factors {ε : ℝ} {N : ℕ} {a b c e : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha : a ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ))) (hb : b ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)))
    (hc : c ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ))) (he0 : 0 ≤ e) (he : e ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ))) :
    a * b * c ^ 2 * e ^ 0 ≤ (3 : ℝ) ^ (ε * (N : ℝ)) ∧
      a * b * c * e ≤ (3 : ℝ) ^ (ε * (N : ℝ)) := by
  set E := (3 : ℝ) ^ (ε / 4 * (N : ℝ)) with hE
  have hE4 : E * E * E * E = (3 : ℝ) ^ (ε * (N : ℝ)) := by
    rw [hE, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hprod : a * b * c * e ≤ E * E * E * E := by
    have h1 : a * b ≤ E * E := mul_le_mul ha hb hb0 (ha0.trans ha)
    have h2 : a * b * c ≤ E * E * E :=
      mul_le_mul h1 hc hc0 (mul_nonneg (ha0.trans ha) (ha0.trans ha))
    exact mul_le_mul h2 he he0 (mul_nonneg (mul_nonneg (ha0.trans ha) (ha0.trans ha))
      (ha0.trans ha))
  have hprod2 : a * b * c ^ 2 * e ^ 0 ≤ E * E * E * E := by
    have := mul_le_mul (mul_le_mul (mul_le_mul ha hb hb0 (ha0.trans ha)) hc hc0
      (mul_nonneg (ha0.trans ha) (ha0.trans ha))) hc hc0
      (mul_nonneg (mul_nonneg (ha0.trans ha) (ha0.trans ha)) (ha0.trans ha))
    calc a * b * c ^ 2 * e ^ 0 = a * b * c * c := by ring
      _ ≤ E * E * E * E := this
  exact ⟨hprod2.trans (le_of_eq hE4), hprod.trans (le_of_eq hE4)⟩

/-- **Assembly at one root.**  From the literal `prop_growth` conclusion `hG` and the
literal clause-2 conclusion `hKe*` at the root, the ChildB body holds. -/
theorem aux_lem_finite_stopping_crude_cost_childB_at_root (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    {σ α β η t C1 : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) (hβα : β ≤ α) (hαβ1 : α - β ≤ 1)
    (hσ : 2 - 2 * α + η ≤ σ) (hC1 : 0 < C1) (h1 : aux_lem_finite_stopping_crude_cost_ClauseOne Jc β C1)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ) (hH1 : 0 < H1)
    (Kg : ℕ → BilateralField d → ℝ) (Cg : Fin 1 → ℝ)
    (hG : aux_lem_finite_stopping_crude_cost_GrowthBody model H z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) t α 1 (fun _ => 1) Kg Cg)
    (Ke : ℕ → BilateralField d → ℝ) (Ce : ℝ)
    (hKe1 : ∀ N, MemLp (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hKe2 : ∀ N, eLpNorm (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Ce)
    (hKe3 : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η om (fun N => Ke N om)) :
    aux_lem_finite_stopping_crude_cost_ChildBRootBody d hd σ model H z j H1 := by
  have : NeZero d := ⟨by omega⟩
  intro ε hε
  set P := (chaosSampleLaw model).toMeasure with hPdef
  -- the finite moment bank: growth constant and grid constant
  have hmem : ∀ (i : Fin 2) (J : ℕ), MemLp (![Kg, Ke] i J) (ENNReal.ofReal 1) P := by
    intro i J
    fin_cases i
    · exact hG.1 0 J
    · exact hKe1 J
  have hbd : ∀ (i : Fin 2) (J : ℕ),
      eLpNorm (![Kg, Ke] i J) (ENNReal.ofReal 1) P ≤ ENNReal.ofReal (max (Cg 0) Ce) := by
    intro i J
    fin_cases i
    · exact (hG.2.1 0 J).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · exact (hKe2 J).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  obtain ⟨Ctail, hCt, hloc⟩ :=
    _root_.SubdiffusiveProcess.Paper.lem_finite_stopping_moments d model 2 1 (max (Cg 0) Ce) le_rfl ![Kg, Ke] hmem hbd
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨N1, hN1⟩ := aux_lem_finite_stopping_crude_cost_exists_nat_const_le_rpow (max (C1 * d) (((3 : ℝ) ^ d) ^ j.toNat)) _ hε4
  refine ⟨Ctail, ε / 4, max (max (4 * j.natAbs) (4 * H1)) N1, hCt, hε4, ?_⟩
  intro N M hN hNM reverse hP phi hphi b hb
  have hNj : 4 * j.natAbs ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNH : 4 * H1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN1 : N1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨Bad0, hBad0m, hBad0P, hBad0⟩ := hloc (ε / 4) hε4 N M
  -- the null set of the two supplier events
  have hGae : ∀ᵐ om ∂P, aux_lem_finite_stopping_crude_cost_GrowthAt model H z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) t α om
      (fun N => Kg N om) ∧ aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η om (fun N => Ke N om) :=
    hG.2.2.2.and hKe3
  set Gc := {om | ¬ (aux_lem_finite_stopping_crude_cost_GrowthAt model H z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) t α om
      (fun N => Kg N om) ∧ aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η om (fun N => Ke N om))} with hGc
  have hGc0 : P Gc = 0 := ae_iff.1 hGae
  refine ⟨Bad0 ∪ toMeasurable P Gc, hBad0m.union (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · calc P (Bad0 ∪ toMeasurable P Gc) ≤ P Bad0 + P (toMeasurable P Gc) := measure_union_le _ _
      _ = P Bad0 := by rw [measure_toMeasurable, hGc0, add_zero]
      _ ≤ ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-1 * (ε / 4) * (N : ℝ))) := hBad0P
      _ = ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-(ε / 4) * (N : ℝ))) := by ring_nf
  intro omega homega
  have hω0 : omega ∉ Bad0 := fun h => homega (Or.inl h)
  have hωG : aux_lem_finite_stopping_crude_cost_GrowthAt model H z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) t α omega
      (fun N => Kg N omega) ∧ aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η omega (fun N => Ke N omega) := by
    by_contra h
    exact homega (Or.inr (subset_toMeasurable P Gc h))
  have hK := hBad0 omega hω0
  have hKgN : |Kg N omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := (hK 0).1
  have hKgM : |Kg M omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := (hK 0).2
  have hKeN : |Ke N omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := (hK 1).1
  have hKeM : |Ke M omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := (hK 1).2
  have hmono : (3 : ℝ) ^ (ε / 4 * (N1 : ℝ)) ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hNN1) hε4.le)
  have hC1d : C1 * d ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) :=
    ((le_max_left _ _).trans hN1).trans hmono
  have h3d : ((3 : ℝ) ^ d) ^ j.toNat ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) :=
    ((le_max_right _ _).trans hN1).trans hmono
  have hE1 : (1 : ℝ) ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hT : N ≤ (if reverse then M else N) := by cases reverse <;> simp [hNM]
  have hKeT : |Ke (if reverse then M else N) omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := by
    cases reverse
    · exact hKeN
    · exact hKeM
  have hKgS : |Kg (if reverse then N else M) omega| ≤ (3 : ℝ) ^ (ε / 4 * (N : ℝ)) := by
    cases reverse
    · exact hKgM
    · exact hKgN
  have hfin := aux_lem_finite_stopping_crude_cost_omega_final hd Jc hβ hβα hαβ1 hσ hC1 h1 z j (zpow_pos (by norm_num) j) H1 hH1
    N hNj hNH (if reverse then M else N) (if reverse then N else M) hT omega
    (fun N => Kg N omega) (fun N => Ke N omega) hωG.1 hωG.2 hP phi hphi b hb
  obtain ⟨hcell, hroot⟩ := hfin
  have hg0 : 0 ≤ c2Norm (closedCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) :
      Set (SpatialCoordinates d)) phi := aux_lem_finite_stopping_crude_cost_c2Norm_nonneg _ _
  have hgg : 0 ≤ c2Norm (closedCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) :
      Set (SpatialCoordinates d)) phi *
      c2Norm (closedCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) :
      Set (SpatialCoordinates d)) phi := mul_nonneg hg0 hg0
  have hC1d0 : 0 ≤ C1 * d := mul_nonneg hC1.le (Nat.cast_nonneg d)
  obtain ⟨hcellc, -⟩ := aux_lem_finite_stopping_crude_cost_four_factors hC1d0 (abs_nonneg _) (abs_nonneg _) hC1d hKeT hKgS
    zero_le_one hE1
  obtain ⟨-, hrootc⟩ := aux_lem_finite_stopping_crude_cost_four_factors (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ d) ^ j.toNat)
    (abs_nonneg _) zero_le_one h3d hKgS hE1 zero_le_one hE1
  refine ⟨fun w0 w => (hcell w0 w).trans ?_, hroot.trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hgg
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (descendantSide_pos _ _
      (descendantSide_pos _ _ (zpow_pos (by norm_num) j))).le _)
    calc C1 * (d : ℝ) * |Ke (if reverse then M else N) omega| *
          |Kg (if reverse then N else M) omega| ^ 2
        = C1 * (d : ℝ) * |Ke (if reverse then M else N) omega| *
          |Kg (if reverse then N else M) omega| ^ 2 * (1 : ℝ) ^ 0 := by ring
      _ ≤ _ := hcellc
  · apply mul_le_mul_of_nonneg_right _ hgg
    calc ((3 : ℝ) ^ d) ^ j.toNat * |Kg (if reverse then N else M) omega|
        = ((3 : ℝ) ^ d) ^ j.toNat * |Kg (if reverse then N else M) omega| * 1 * 1 := by ring
      _ ≤ _ := hrootc

/-! ## The two main theorems -/

/-- Fixed aux_lem_finite_stopping_crude_cost_exponents from `σ` (`d - s₀ < ϑ/8`, `s₀ = d - 2 + 2α - η₀`). -/
theorem aux_lem_finite_stopping_crude_cost_exponents (σ : ℝ) (hσ : 0 < σ) :
    let σ' := min σ 1
    (5 / 8 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧ (5 / 8 : ℝ) ≤ 1 - σ' / 4 ∧
      (1 - σ' / 4) - 5 / 8 ≤ 1 ∧ 2 - 2 * (1 - σ' / 4) + σ' / 2 ≤ σ ∧
      0 < 1 - σ' / 4 ∧ 1 - σ' / 4 < 1 ∧ 0 < σ' / 2 := by
  intro σ'
  have h1 : σ' ≤ 1 := min_le_right _ _
  have h2 : σ' ≤ σ := min_le_left _ _
  have h3 : 0 < σ' := lt_min hσ one_pos
  refine ⟨⟨by norm_num, by norm_num⟩, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- Clause 2 of `lem_extension` with the single grid family `{z + 3^(-k) ℤ^d}`. -/
theorem aux_lem_finite_stopping_crude_cost_clauseTwo_of [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (z : SpatialCoordinates d) (j : ℤ)
    (β η : ℝ) (Ke : ℕ → BilateralField d → ℝ)
    (h : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      ∀ (N k : ℕ) (index : Fin 1) (nidx : Fin d → ℤ), k ≤ N →
        (centeredCube (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
          centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)) →
        Jc.Lam z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)
            (cutoffPositiveCoefficient model H om N z (zpow_pos (by norm_num) j))
            (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((β - 1 / 2) / 4) 2 +
          (Jc.lam z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)
            (cutoffPositiveCoefficient model H om N z (zpow_pos (by norm_num) j))
            (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((β - 1 / 2) / 4) 2)⁻¹ ≤
          Ke N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-η)) :
    ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η om (fun N => Ke N om) :=
  h.mono fun _ hom N k nidx hk hsub => hom N k 0 nidx hk hsub

/-- **ChildB, proved** (roots of side `≤ 1`): from the stated standing inputs, via
`lem_extension` (clauses 1, 2), `prop_growth` and `lem_finite_stopping_moments`. -/
theorem aux_lem_finite_stopping_crude_cost_childB_le (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) : aux_lem_finite_stopping_crude_cost_ChildBInLe d hd Jc := by
  intro σ hσ
  obtain ⟨hβ, hβα, hαβ1, hσ', hα0, hα1, hη⟩ := aux_lem_finite_stopping_crude_cost_exponents σ hσ
  have hext := _root_.SubdiffusiveProcess.Paper.lem_extension d hd Jc Xc Sf
  obtain ⟨C1, hC1, h1⟩ := hext.1 (5 / 8) hβ
  obtain ⟨δe, hδe, hE⟩ := hext.2 (min σ 1 / 2) 1 hη le_rfl (5 / 8) hβ
  obtain ⟨δg, hδg, hGr⟩ := aux_lem_finite_stopping_crude_cost_growthBody_of_prop_growth hd Jc Pc Xc W Cp Sf
    ((d : ℝ) - 1 / 2) (1 - min σ 1 / 4) 1 (fun _ => 1) (by linarith) (by linarith) hα0 hα1
    (fun _ => le_rfl)
  refine ⟨min δe δg, lt_min hδe hδg, ?_⟩
  intro model Rm Sreg It H hH hsmall z j hj H1 hH1
  obtain ⟨Kg, Cg, hG⟩ := hGr model Rm Sreg It H hH (hsmall.trans (min_le_right _ _))
    z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) (zpow_le_one_of_nonpos₀ (by norm_num) hj)
  obtain ⟨Ke, Ce, hKe1, hKe2, hKe3⟩ := hE model Rm H hH (hsmall.trans (min_le_left _ _))
    z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) 1 (fun _ => z)
  exact aux_lem_finite_stopping_crude_cost_childB_at_root hd Jc hβ hβα hαβ1 hσ' hC1 h1 model H z j H1 hH1 Kg Cg hG Ke Ce
    hKe1 hKe2 (aux_lem_finite_stopping_crude_cost_clauseTwo_of Jc z j (5 / 8) (min σ 1 / 2) Ke hKe3)

/-- **ChildB for every triadic root**, from the same suppliers and the exact missing
supplier `aux_lem_finite_stopping_crude_cost_LargeRootGrowth` (`prop_growth` on cubes of side `> 1`). -/
theorem aux_lem_finite_stopping_crude_cost_childB_of_large (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (hL : aux_lem_finite_stopping_crude_cost_LargeRootGrowth d Jc) : aux_lem_finite_stopping_crude_cost_ChildBIn d hd Jc := by
  intro σ hσ
  obtain ⟨hβ, hβα, hαβ1, hσ', hα0, hα1, hη⟩ := aux_lem_finite_stopping_crude_cost_exponents σ hσ
  have hext := _root_.SubdiffusiveProcess.Paper.lem_extension d hd Jc Xc Sf
  obtain ⟨C1, hC1, h1⟩ := hext.1 (5 / 8) hβ
  obtain ⟨δe, hδe, hE⟩ := hext.2 (min σ 1 / 2) 1 hη le_rfl (5 / 8) hβ
  obtain ⟨δg, hδg, hGr⟩ := aux_lem_finite_stopping_crude_cost_growthBody_of_prop_growth hd Jc Pc Xc W Cp Sf
    ((d : ℝ) - 1 / 2) (1 - min σ 1 / 4) 1 (fun _ => 1) (by linarith) (by linarith) hα0 hα1
    (fun _ => le_rfl)
  obtain ⟨δL, hδL, hGL⟩ := hL ((d : ℝ) - 1 / 2) (1 - min σ 1 / 4) 1 (fun _ => 1)
    (by linarith) (by linarith) hα0 hα1 (fun _ => le_rfl)
  refine ⟨min δe (min δg δL), lt_min hδe (lt_min hδg hδL), ?_⟩
  intro model Rm Sreg It H hH hsmall z j H1 hH1
  have hG' : ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin 1 → ℝ),
      aux_lem_finite_stopping_crude_cost_GrowthBody model H z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) ((d : ℝ) - 1 / 2)
        (1 - min σ 1 / 4) 1 (fun _ => 1) K Cbound := by
    by_cases hj : j ≤ 0
    · exact hGr model Rm Sreg It H hH
        (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
        z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) (zpow_le_one_of_nonpos₀ (by norm_num) hj)
    · exact hGL model Rm Sreg It H hH
        (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
        z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) (one_lt_zpow₀ (by norm_num) (by omega))
  obtain ⟨Kg, Cg, hG⟩ := hG'
  obtain ⟨Ke, Ce, hKe1, hKe2, hKe3⟩ := hE model Rm H hH (hsmall.trans (min_le_left _ _))
    z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j) 1 (fun _ => z)
  exact aux_lem_finite_stopping_crude_cost_childB_at_root hd Jc hβ hβα hαβ1 hσ' hC1 h1 model H z j H1 hH1 Kg Cg hG Ke Ce
    hKe1 hKe2 (aux_lem_finite_stopping_crude_cost_clauseTwo_of Jc z j (5 / 8) (min σ 1 / 2) Ke hKe3)




theorem aux_lem_finite_stopping_crude_cost_largeRootGrowth (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d) :
    aux_lem_finite_stopping_crude_cost_LargeRootGrowth d Jc := by
  intro t alpha k ps h1 h2 h3 h4 h5
  exact _root_.SubdiffusiveProcess.Paper.prop_growth_large_root d hd Jc Pc Xc W Cp Sf t alpha k ps h1 h2 h3 h4 h5




theorem lem_finite_stopping_crude_cost
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d) :
    ∀ σ : ℝ, 0 < σ → ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d model)
      (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ), 0 < H1 →
      aux_lem_finite_stopping_crude_cost_ChildBRootBody d hd σ model H z j H1 :=
  aux_lem_finite_stopping_crude_cost_childB_of_large hd Jc Pc Xc Sf W Cp
    (aux_lem_finite_stopping_crude_cost_largeRootGrowth hd Jc Pc Xc Sf W Cp)

end SubdiffusiveProcess.Paper
