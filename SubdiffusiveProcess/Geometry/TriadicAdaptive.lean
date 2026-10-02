import SubdiffusiveProcess.Geometry.TriadicNesting

/-!
# The actual retained and unresolved triadic cells

A cell is retained at generation `J+1` precisely when its parent was
unresolved and it avoids every active midplane. The old unresolved region
is the disjoint union of this retained region and the new unresolved
region, up to Lebesgue null sets.
-/

open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- A fine cell meeting an active midplane has a parent meeting that same midplane. -/
theorem triadicParent_mem_unresolved (J : ℕ) (I : Finset (Fin d))
    {k : OddGridIndex d (triadicHalf (J + 1))}
    (hk : k ∈ oddGridUnresolved (triadicHalf (J + 1)) I) :
    triadicParent J k ∈ oddGridUnresolved (triadicHalf J) I := by
  simp only [oddGridUnresolved, Finset.mem_biUnion, oddGridPlaneCells,
    Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  obtain ⟨i, hi, hki⟩ := hk
  refine ⟨i, hi, ?_⟩
  change (k i).val / 3 = triadicHalf J
  have hm := triadicHalf_succ J
  omega

/-- The union of fine children of a finite parent family covers exactly that family a.e. -/
theorem triadicRefinement_union_ae_eq (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (J : ℕ) (S : Finset (OddGridIndex d (triadicHalf J))) :
    (⋃ k : OddGridIndex d (triadicHalf (J + 1)), ⋃ _ : triadicParent J k ∈ S,
      (oddGridCell z r hr (triadicHalf (J + 1)) k : Set (SpatialCoordinates d)))
      =ᵐ[volume] (⋃ k ∈ S, (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) := by
  filter_upwards [ae_all_iff.mpr (fun k => triadicChildren_union_ae_eq z hr J k)] with x hx
  apply propext
  change (x ∈ (⋃ k : OddGridIndex d (triadicHalf (J + 1)),
    ⋃ _ : triadicParent J k ∈ S,
      (oddGridCell z r hr (triadicHalf (J + 1)) k : Set (SpatialCoordinates d)))) ↔
    x ∈ (⋃ k ∈ S, (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)))
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hk, hxk⟩
    refine ⟨triadicParent J k, hk, ?_⟩
    exact triadicCell_subset_parent z hr J k hxk
  · rintro ⟨k, hk, hxk⟩
    have hxchildren : x ∈ ⋃ l : OddGridIndex d 1,
        (oddGridCell z r hr (triadicHalf (J + 1)) (triadicChild J k l) : Set (SpatialCoordinates d)) :=
      (hx k).mpr hxk
    obtain ⟨l, hxl⟩ := mem_iUnion.mp hxchildren
    exact ⟨triadicChild J k l, by simpa only [triadicParent_child] using hk, hxl⟩

/-- Cells first retained at generation `J+1`. -/
def triadicRetainedLabels (J : ℕ) (I : Finset (Fin d)) :
    Finset (OddGridIndex d (triadicHalf (J + 1))) :=
  Finset.univ.filter (fun k => triadicParent J k ∈ oddGridUnresolved (triadicHalf J) I ∧
    k ∉ oddGridUnresolved (triadicHalf (J + 1)) I)

/-- The actual unresolved region after `J` refinements. -/
def triadicUnresolvedRegion (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I : Finset (Fin d)) (J : ℕ) : Set (SpatialCoordinates d) :=
  ⋃ k ∈ oddGridUnresolved (triadicHalf J) I,
    (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))

/-- The actual cells first retained at generation `J+1`. -/
def triadicRetainedRegion (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I : Finset (Fin d)) (J : ℕ) : Set (SpatialCoordinates d) :=
  ⋃ k ∈ triadicRetainedLabels J I,
    (oddGridCell z r hr (triadicHalf (J + 1)) k : Set (SpatialCoordinates d))

/-- All unresolved cells lie in the original root. -/
theorem triadicUnresolvedRegion_subset_root (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    triadicUnresolvedRegion z r hr I J ⊆ centeredCube z r hr :=
  iUnion_subset (fun k => iUnion_subset (fun _ => oddGridCell_subset z hr _ k))

/-- Unresolved regions are nested as refinement proceeds. -/
theorem triadicUnresolvedRegion_succ_subset (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    triadicUnresolvedRegion z r hr I (J + 1) ⊆ triadicUnresolvedRegion z r hr I J := by
  intro x hx
  simp only [triadicUnresolvedRegion, mem_iUnion] at hx
  obtain ⟨k, hk, hxk⟩ := hx
  exact mem_iUnion.mpr ⟨triadicParent J k, mem_iUnion.mpr
    ⟨triadicParent_mem_unresolved J I hk, triadicCell_subset_parent z hr J k hxk⟩⟩

/-- A newly retained cell lies in the preceding unresolved region. -/
theorem triadicRetainedRegion_subset_previous (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    triadicRetainedRegion z r hr I J ⊆ triadicUnresolvedRegion z r hr I J := by
  intro x hx
  simp only [triadicRetainedRegion, mem_iUnion] at hx
  obtain ⟨k, hk, hxk⟩ := hx
  have hp := (Finset.mem_filter.mp hk).2.1
  exact mem_iUnion.mpr ⟨triadicParent J k, mem_iUnion.mpr
    ⟨hp, triadicCell_subset_parent z hr J k hxk⟩⟩

/-- Retained and unresolved cells at the same new depth are disjoint. -/
theorem triadicRetainedRegion_disjoint_next (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    Disjoint (triadicRetainedRegion z r hr I J) (triadicUnresolvedRegion z r hr I (J + 1)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [triadicRetainedRegion, mem_iUnion] at hx
  obtain ⟨k, hk, hxk⟩ := hx
  simp only [triadicUnresolvedRegion, mem_iUnion] at hy
  obtain ⟨l, hl, hxl⟩ := hy
  have hkl : k ≠ l := by
    intro h
    subst l
    exact (Finset.mem_filter.mp hk).2.2 hl
  exact Set.disjoint_left.mp (oddGridCell_pairwiseDisjoint z hr _ hkl) hxk hxl

/-- One actual refinement step separates retained cells and the new unresolved cells. -/
theorem triadicAdaptive_step_ae_eq (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (I : Finset (Fin d)) (J : ℕ) :
    (triadicRetainedRegion z r hr I J ∪ triadicUnresolvedRegion z r hr I (J + 1) :
      Set (SpatialCoordinates d)) =ᵐ[volume] triadicUnresolvedRegion z r hr I J := by
  have he : triadicRetainedRegion z r hr I J ∪ triadicUnresolvedRegion z r hr I (J + 1) =
      ⋃ k : OddGridIndex d (triadicHalf (J + 1)),
        ⋃ _ : triadicParent J k ∈ oddGridUnresolved (triadicHalf J) I,
          (oddGridCell z r hr (triadicHalf (J + 1)) k : Set (SpatialCoordinates d)) := by
    ext x
    simp only [triadicRetainedRegion, triadicUnresolvedRegion, mem_union, mem_iUnion,
      triadicRetainedLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨k, ⟨hk, _⟩, hx⟩ | ⟨k, hk, hx⟩)
      · exact ⟨k, hk, hx⟩
      · exact ⟨k, triadicParent_mem_unresolved J I hk, hx⟩
    · rintro ⟨k, hk, hx⟩
      by_cases hu : k ∈ oddGridUnresolved (triadicHalf (J + 1)) I
      · exact Or.inr ⟨k, hu, hx⟩
      · exact Or.inl ⟨k, ⟨hk, hu⟩, hx⟩
  rw [he]
  exact triadicRefinement_union_ae_eq z hr J _

end SubdiffusiveProcess
