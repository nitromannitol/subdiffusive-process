import SubdiffusiveProcess.Geometry.BoundaryPartitions
import SubdiffusiveProcess.Geometry.ClosedOddGridCover

/-!
# Finite triadic leaf trees along a boundary set

Labels are triadic grid labels of a fixed root cube. The leaves at horizon `n` of the stopped
refinement started at depth `J0` are the cells of depth in `[J0, J0+n]` whose closure misses the
boundary set `S` (or which sit at the last depth), and whose parent's closure meets `S`
(or which sit at the first depth). This module proves the tree-shaped properties:
disjointness, closed and almost-everywhere covers, and persistence.
-/
open Set MeasureTheory TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

/-- The parent label; a depth-zero label is its own parent. -/
def triadicParentLabel : TriadicGridLabel d → TriadicGridLabel d
  | ⟨0, k⟩ => ⟨0, k⟩
  | ⟨J + 1, k⟩ => ⟨J, triadicParent J k⟩

/-- The open cell of a label, as a set. -/
def triadicCell (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (q : TriadicGridLabel d) :
    Set (SpatialCoordinates d) := (triadicGridCell z R hR q : Set (SpatialCoordinates d))

/-- The `m`-th ancestor label. -/
def triadicAncestorAt (m : ℕ) (q : TriadicGridLabel d) : TriadicGridLabel d :=
  triadicParentLabel^[m] q

/-- The closure of the cell of `q` misses the boundary set `S`. -/
def TriadicMisses (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : Set (SpatialCoordinates d)) (q : TriadicGridLabel d) : Prop :=
  Disjoint (closure (triadicCell z R hR q)) S

/-- Membership in the leaf set of horizon `n` of the refinement started at depth `J0`. -/
def TriadicIsLeaf (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : Set (SpatialCoordinates d)) (J0 n : ℕ) (q : TriadicGridLabel d) : Prop :=
  J0 ≤ q.1 ∧ q.1 ≤ J0 + n ∧ (TriadicMisses z R hR S q ∨ q.1 = J0 + n) ∧
    (q.1 = J0 ∨ ¬ TriadicMisses z R hR S (triadicParentLabel q))

/-- The finite leaf set of horizon `n`. -/
def triadicLeaves (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : Set (SpatialCoordinates d)) (J0 n : ℕ) : Finset (TriadicGridLabel d) :=
  ((Finset.range (J0 + n + 1)).sigma
    (fun J => (Finset.univ : Finset (OddGridIndex d (triadicHalf J))))).filter
    (TriadicIsLeaf z R hR S J0 n)

variable (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)

theorem triadicCell_eq_oddGridCell (J : ℕ) (k : OddGridIndex d (triadicHalf J)) :
    triadicCell z R hR ⟨J, k⟩ =
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) := rfl

theorem triadicGridSide_eq (q : TriadicGridLabel d) : triadicGridSide R q = R / (3 : ℝ) ^ q.1 := by
  unfold triadicGridSide
  rw [triadic_denominator]

theorem triadicCell_subset_root (q : TriadicGridLabel d) :
    triadicCell z R hR q ⊆ centeredCube z R hR := triadicGridCell_subset z hR q

theorem triadicParentLabel_depth (q : TriadicGridLabel d) :
    (triadicParentLabel q).1 = q.1 - 1 := by
  obtain ⟨_ | J, k⟩ := q <;> rfl

theorem triadicCell_subset_parentLabel (q : TriadicGridLabel d) :
    triadicCell z R hR q ⊆ triadicCell z R hR (triadicParentLabel q) := by
  obtain ⟨_ | J, k⟩ := q
  · exact subset_rfl
  · exact SubdiffusiveProcess.triadicCell_subset_parent z hR J k

theorem triadicAncestorAt_succ (m : ℕ) (q : TriadicGridLabel d) :
    triadicAncestorAt (m + 1) q = triadicAncestorAt m (triadicParentLabel q) := by
  simp only [triadicAncestorAt, Function.iterate_succ, Function.comp_apply]

theorem triadicAncestorAt_depth (m : ℕ) (q : TriadicGridLabel d) :
    (triadicAncestorAt m q).1 = q.1 - m := by
  induction m generalizing q with
  | zero => rfl
  | succ m ih =>
    rw [triadicAncestorAt_succ, ih, triadicParentLabel_depth]
    omega

theorem triadicCell_subset_ancestorAt (m : ℕ) (q : TriadicGridLabel d) :
    triadicCell z R hR q ⊆ triadicCell z R hR (triadicAncestorAt m q) := by
  induction m generalizing q with
  | zero => exact subset_rfl
  | succ m ih =>
    rw [triadicAncestorAt_succ]
    exact (triadicCell_subset_parentLabel z R hR q).trans (ih _)

theorem triadicAncestorAt_succ' (m : ℕ) (q : TriadicGridLabel d) :
    triadicAncestorAt (m + 1) q = triadicParentLabel (triadicAncestorAt m q) := by
  simp only [triadicAncestorAt, Function.iterate_succ_apply']

/-- Two cells of the same depth that are not disjoint are the same label. -/
theorem triadicLabel_eq_of_not_disjoint (a q : TriadicGridLabel d) (h : a.1 = q.1)
    (hne : ¬ Disjoint (triadicCell z R hR a) (triadicCell z R hR q)) : a = q := by
  obtain ⟨Ja, ka⟩ := a
  obtain ⟨Jq, kq⟩ := q
  simp only at h
  subst h
  by_contra hne'
  have hk : ka ≠ kq := fun hk => hne' (by rw [hk])
  exact hne (oddGridCell_pairwiseDisjoint z hR (triadicHalf Ja) hk)

theorem TriadicMisses.of_parent {S : Set (SpatialCoordinates d)} {q : TriadicGridLabel d}
    (h : TriadicMisses z R hR S (triadicParentLabel q)) : TriadicMisses z R hR S q :=
  Set.disjoint_of_subset_left (closure_mono (triadicCell_subset_parentLabel z R hR q)) h

theorem mem_triadicLeaves {S : Set (SpatialCoordinates d)} {J0 n : ℕ} {q : TriadicGridLabel d} :
    q ∈ triadicLeaves z R hR S J0 n ↔ TriadicIsLeaf z R hR S J0 n q := by
  unfold triadicLeaves
  rw [Finset.mem_filter, Finset.mem_sigma]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨Finset.mem_range.2 (by have := h.2.1; omega), Finset.mem_univ _⟩, h⟩

/-- Every deepest cell lies inside a leaf. -/
theorem triadicPart_exists_leaf_above (S : Set (SpatialCoordinates d)) (J0 n : ℕ) (q : TriadicGridLabel d)
    (hq : q.1 = J0 + n) :
    ∃ ℓ ∈ triadicLeaves z R hR S J0 n, triadicCell z R hR q ⊆ triadicCell z R hR ℓ := by
  let P : ℕ → Prop := fun m => m = 0 ∨ TriadicMisses z R hR S (triadicAncestorAt m q)
  have hP0 : P 0 := Or.inl rfl
  have hspec : P (Nat.findGreatest P n) := Nat.findGreatest_spec (Nat.zero_le n) hP0
  have hle : Nat.findGreatest P n ≤ n := Nat.findGreatest_le n
  set m := Nat.findGreatest P n with hm
  refine ⟨triadicAncestorAt m q, ?_, triadicCell_subset_ancestorAt z R hR m q⟩
  rw [mem_triadicLeaves]
  have hdep := triadicAncestorAt_depth m q
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases hspec with h0 | hmiss
    · right
      rw [hdep]
      omega
    · exact Or.inl hmiss
  · by_cases hmn : m = n
    · left
      rw [hdep]
      omega
    · right
      have hnot : ¬ P (m + 1) :=
        Nat.findGreatest_is_greatest (show Nat.findGreatest P n < m + 1 by omega) (by omega)
      have := hnot
      simp only [P, not_or] at this
      rw [← triadicAncestorAt_succ']
      exact this.2

theorem triadicLeaves_disjoint_of_depth_lt (S : Set (SpatialCoordinates d)) (J0 n : ℕ)
    {a b : TriadicGridLabel d} (ha : a ∈ triadicLeaves z R hR S J0 n)
    (hb : b ∈ triadicLeaves z R hR S J0 n) (hlt : a.1 < b.1) :
    Disjoint (triadicCell z R hR a) (triadicCell z R hR b) := by
  by_contra hnd
  rw [mem_triadicLeaves] at ha hb
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  obtain ⟨m, hm⟩ : ∃ m, b.1 - a.1 = m + 1 := ⟨b.1 - a.1 - 1, by omega⟩
  have hdep : (triadicAncestorAt (m + 1) b).1 = a.1 := by
    rw [triadicAncestorAt_depth]; omega
  have hsub := triadicCell_subset_ancestorAt z R hR (m + 1) b
  have hne : ¬ Disjoint (triadicCell z R hR a) (triadicCell z R hR (triadicAncestorAt (m + 1) b)) :=
    fun h => hnd (Set.disjoint_of_subset_right hsub h)
  have heq := triadicLabel_eq_of_not_disjoint z R hR a _ hdep.symm hne
  have hpar : ¬ TriadicMisses z R hR S (triadicParentLabel b) := by
    rcases hb4 with h | h
    · omega
    · exact h
  apply hpar
  have hsub2 := triadicCell_subset_ancestorAt z R hR m (triadicParentLabel b)
  rw [← triadicAncestorAt_succ, ← heq] at hsub2
  have hmiss : TriadicMisses z R hR S a := by
    rcases ha3 with h | h
    · exact h
    · omega
  exact Set.disjoint_of_subset_left (closure_mono hsub2) hmiss

/-- Distinct leaves have disjoint open cells. -/
theorem triadicLeaves_disjoint (S : Set (SpatialCoordinates d)) (J0 n : ℕ)
    {a b : TriadicGridLabel d} (ha : a ∈ triadicLeaves z R hR S J0 n)
    (hb : b ∈ triadicLeaves z R hR S J0 n) (hab : a ≠ b) :
    Disjoint (triadicCell z R hR a) (triadicCell z R hR b) := by
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact triadicLeaves_disjoint_of_depth_lt z R hR S J0 n ha hb h
  · by_contra hnd
    exact hab (triadicLabel_eq_of_not_disjoint z R hR a b h hnd)
  · exact (triadicLeaves_disjoint_of_depth_lt z R hR S J0 n hb ha h).symm

/-- The closed leaves cover the closed root. -/
theorem triadicLeaves_closure_cover (S : Set (SpatialCoordinates d)) (J0 n : ℕ) :
    (⋃ ℓ ∈ triadicLeaves z R hR S J0 n, closure (triadicCell z R hR ℓ)) =
      closure (centeredCube z R hR : Set (SpatialCoordinates d)) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨ℓ, -, hxℓ⟩ := mem_iUnion₂.1 hx
    exact closure_mono (triadicCell_subset_root z R hR ℓ) hxℓ
  · intro x hx
    rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (triadicHalf (J0 + n))] at hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    obtain ⟨ℓ, hℓ, hsub⟩ := triadicPart_exists_leaf_above z R hR S J0 n ⟨J0 + n, k⟩ rfl
    exact mem_iUnion₂.2 ⟨ℓ, hℓ, closure_mono hsub hk⟩

/-- The open leaves cover the root almost everywhere. -/
theorem triadicLeaves_cover_ae (S : Set (SpatialCoordinates d)) (J0 n : ℕ) :
    (⋃ ℓ ∈ triadicLeaves z R hR S J0 n, triadicCell z R hR ℓ) =ᵐ[volume]
      (centeredCube z R hR : Set (SpatialCoordinates d)) := by
  have hV := oddGrid_union_ae_eq z hR (triadicHalf (J0 + n))
  have hVU : (⋃ k : OddGridIndex d (triadicHalf (J0 + n)),
      (oddGridCell z R hR (triadicHalf (J0 + n)) k : Set (SpatialCoordinates d))) ⊆
      ⋃ ℓ ∈ triadicLeaves z R hR S J0 n, triadicCell z R hR ℓ := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    obtain ⟨ℓ, hℓ, hsub⟩ := triadicPart_exists_leaf_above z R hR S J0 n ⟨J0 + n, k⟩ rfl
    exact mem_iUnion₂.2 ⟨ℓ, hℓ, hsub hk⟩
  have hUQ : (⋃ ℓ ∈ triadicLeaves z R hR S J0 n, triadicCell z R hR ℓ) ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    intro x hx
    obtain ⟨ℓ, -, hxℓ⟩ := mem_iUnion₂.1 hx
    exact triadicCell_subset_root z R hR ℓ hxℓ
  refine ae_eq_set.2 ⟨by simp [diff_eq_empty.2 hUQ], ?_⟩
  exact measure_mono_null (Set.diff_subset_diff_right hVU) (ae_eq_set.1 hV).2

/-- Boundary points of `S` lie in closed leaves of the last depth. -/
theorem triadicLeaves_boundary (S : Set (SpatialCoordinates d)) (J0 n : ℕ)
    {x : SpatialCoordinates d} (hxS : x ∈ S)
    (hx : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ ℓ ∈ triadicLeaves z R hR S J0 n, x ∈ closure (triadicCell z R hR ℓ) ∧ ℓ.1 = J0 + n := by
  rw [← triadicLeaves_closure_cover z R hR S J0 n] at hx
  obtain ⟨ℓ, hℓ, hxℓ⟩ := mem_iUnion₂.1 hx
  refine ⟨ℓ, hℓ, hxℓ, ?_⟩
  rw [mem_triadicLeaves] at hℓ
  rcases hℓ.2.2.1 with h | h
  · exact absurd hxS (fun hxS => Set.disjoint_left.1 h hxℓ hxS)
  · exact h

/-- Persistence between two horizons `n ≤ m`. -/
theorem triadicLeaves_persistence (S : Set (SpatialCoordinates d)) (J0 : ℕ) {n m : ℕ}
    (hnm : n ≤ m) {x : SpatialCoordinates d}
    (hx : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d))) :
    (∃ a ∈ triadicLeaves z R hR S J0 n, a ∈ triadicLeaves z R hR S J0 m ∧
        x ∈ closure (triadicCell z R hR a)) ∨
      (∃ a ∈ triadicLeaves z R hR S J0 n, ∃ b ∈ triadicLeaves z R hR S J0 m,
        x ∈ closure (triadicCell z R hR a) ∧ x ∈ closure (triadicCell z R hR b) ∧
        J0 + n ≤ a.1 ∧ J0 + n ≤ b.1) := by
  have hxm := hx
  rw [← triadicLeaves_closure_cover z R hR S J0 m] at hxm
  obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 hxm
  have hxn := hx
  rw [← triadicLeaves_closure_cover z R hR S J0 n] at hxn
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 hxn
  have hb' := (mem_triadicLeaves z R hR).1 hb
  have ha' := (mem_triadicLeaves z R hR).1 ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb'
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha'
  by_cases hbd : J0 + n ≤ b.1
  · by_cases haL : a ∈ triadicLeaves z R hR S J0 m
    · exact Or.inl ⟨a, ha, haL, hxa⟩
    · right
      refine ⟨a, ha, b, hb, hxa, hxb, ?_, hbd⟩
      by_contra hlt
      apply haL
      rw [mem_triadicLeaves]
      refine ⟨ha1, by omega, ?_, ha4⟩
      rcases ha3 with h | h
      · exact Or.inl h
      · omega
  · left
    refine ⟨b, ?_, hb, hxb⟩
    rw [mem_triadicLeaves]
    refine ⟨hb1, by omega, ?_, hb4⟩
    rcases hb3 with h | h
    · exact Or.inl h
    · omega

end SubdiffusiveProcess
