module

public import SubdiffusiveProcess.Geometry.TriadicPartition

@[expose] public section

/-!
# A finite family of the actual mixed-depth partition cubes

The left labels select first-retained cells at generations `1,...,J`;
the right labels select unresolved cells at depth `J`. This finite family
is suitable for the finite-partition response inequalities: its actual
open cubes are disjoint, cover the root almost everywhere and have volume
weights summing to one.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- Tags distinguish retained generations from the final unresolved depth. -/
abbrev TriadicAdaptiveIndex (d J : ℕ) :=
  (Σ j : Fin J, OddGridIndex d (triadicHalf (j.val + 1))) ⊕ OddGridIndex d (triadicHalf J)

/-- The literal retained and unresolved labels in the depth-`J` adaptive partition. -/
def triadicAdaptiveLabels (I : Finset (Fin d)) (J : ℕ) : Finset (TriadicAdaptiveIndex d J) := by
  classical
  exact Finset.univ.filter (fun t => match t with
    | Sum.inl ⟨j, k⟩ => k ∈ triadicRetainedLabels j.val I
    | Sum.inr k => k ∈ oddGridUnresolved (triadicHalf J) I)

/-- The actual open cube belonging to a tagged adaptive-partition label. -/
def triadicAdaptiveCell (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (J : ℕ) :
    TriadicAdaptiveIndex d J → Opens (SpatialCoordinates d)
  | Sum.inl ⟨j, k⟩ => oddGridCell z r hr (triadicHalf (j.val + 1)) k
  | Sum.inr k => oddGridCell z r hr (triadicHalf J) k

/-- Every labeled adaptive cell lies in the original root. -/
theorem triadicAdaptiveCell_subset_root (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (J : ℕ) (t : TriadicAdaptiveIndex d J) :
    (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d)) ⊆ centeredCube z r hr := by
  rcases t with ⟨j, k⟩ | k <;> exact oddGridCell_subset z hr _ k

/-- Every actual adaptive cell is bounded. -/
theorem triadicAdaptiveCell_isBounded (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (J : ℕ) (t : TriadicAdaptiveIndex d J) :
    Bornology.IsBounded (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d)) := by
  exact (centeredCube_isBounded z hr).subset (triadicAdaptiveCell_subset_root z hr J t)

/-- Every actual adaptive cell has strictly positive real volume. -/
theorem triadicAdaptiveCell_volume_pos (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (J : ℕ) (t : TriadicAdaptiveIndex d J) :
    0 < volume.real (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d)) := by
  rcases t with ⟨j, k⟩ | k <;> exact centeredCube_volume_pos _ (div_pos hr (by positivity))

instance triadicAdaptiveCell_isFiniteMeasure (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (J : ℕ) (t : TriadicAdaptiveIndex d J) :
    IsFiniteMeasure (volume.restrict (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d))) :=
  isFiniteMeasure_restrict.mpr (measure_ne_top_of_subset
    (triadicAdaptiveCell_subset_root z hr J t)
    (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top))

/-- The finite family is exactly the union of retained generations and the final unresolved region. -/
theorem triadicAdaptiveCells_union (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (I : Finset (Fin d)) (J : ℕ) :
    (⋃ t ∈ triadicAdaptiveLabels I J,
      (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d))) =
    (⋃ j ∈ Finset.range J, triadicRetainedRegion z r hr I j) ∪
      triadicUnresolvedRegion z r hr I J := by
  classical
  ext x
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨t, ht, hx⟩
    have ht' := (Finset.mem_filter.mp ht).2
    rcases t with ⟨j, k⟩ | k
    · exact Or.inl ⟨j.val, Finset.mem_range.mpr j.isLt,
        mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨ht', hx⟩⟩⟩
    · exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨ht', hx⟩⟩)
  · rintro (⟨j, hj, hx⟩ | hx)
    · simp only [triadicRetainedRegion, mem_iUnion] at hx
      obtain ⟨k, hk, hx⟩ := hx
      refine ⟨Sum.inl ⟨⟨j, Finset.mem_range.mp hj⟩, k⟩, ?_, hx⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    · simp only [triadicUnresolvedRegion, mem_iUnion] at hx
      obtain ⟨k, hk, hx⟩ := hx
      exact ⟨Sum.inr k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, hx⟩

/-- Distinct selected labels represent disjoint actual open cubes, including across depths. -/
theorem triadicAdaptiveCells_pairwiseDisjoint (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    (triadicAdaptiveLabels I J : Set (TriadicAdaptiveIndex d J)).PairwiseDisjoint
      (fun t => (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d))) := by
  classical
  have hret : ∀ j (k : OddGridIndex d (triadicHalf (j + 1))),
      k ∈ triadicRetainedLabels j I →
      (oddGridCell z r hr (triadicHalf (j + 1)) k : Set (SpatialCoordinates d)) ⊆
        triadicRetainedRegion z r hr I j := by
    intro j k hk x hx
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, hx⟩⟩
  have hun : ∀ (k : OddGridIndex d (triadicHalf J)),
      k ∈ oddGridUnresolved (triadicHalf J) I →
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆
        triadicUnresolvedRegion z r hr I J := by
    intro k hk x hx
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, hx⟩⟩
  intro t ht s hs hts
  have ht' := (Finset.mem_filter.mp ht).2
  have hs' := (Finset.mem_filter.mp hs).2
  rcases t with ⟨j, k⟩ | k <;> rcases s with ⟨j', k'⟩ | k'
  · by_cases hj : j = j'
    · subst j'
      apply oddGridCell_pairwiseDisjoint z hr _
      intro hk
      subst k'
      exact hts rfl
    · have hjv : j.val ≠ j'.val := fun h => hj (Fin.ext h)
      exact (triadicRetainedRegion_pairwiseDisjoint z hr I hjv).mono
        (hret j.val k ht') (hret j'.val k' hs')
  · exact (triadicRetainedRegion_disjoint_unresolved z hr I j.isLt).mono
      (hret j.val k ht') (hun k' hs')
  · exact ((triadicRetainedRegion_disjoint_unresolved z hr I j'.isLt).mono
      (hret j'.val k' hs') (hun k ht')).symm
  · apply oddGridCell_pairwiseDisjoint z hr _
    intro hk
    subst k'
    exact hts rfl

/-- The finite family covers the actual root up to Lebesgue null sets. -/
theorem triadicAdaptiveCells_union_ae_eq (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) {I : Finset (Fin d)} (hI : I.Nonempty) (J : ℕ) :
    (⋃ t ∈ triadicAdaptiveLabels I J,
      (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d)))
      =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [triadicAdaptiveCells_union]
  exact triadicAdaptive_partition_ae_eq z hr hI J

/-- The sum of the actual selected cell volumes is the root volume. -/
theorem triadicAdaptiveCells_sum_volume (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) {I : Finset (Fin d)} (hI : I.Nonempty) (J : ℕ) :
    (∑ t ∈ triadicAdaptiveLabels I J,
      volume.real (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d))) =
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [← measureReal_biUnion_finset (triadicAdaptiveCells_pairwiseDisjoint z hr I J)
    (fun t _ => (triadicAdaptiveCell z r hr J t).isOpen.measurableSet)
    (fun t _ => measure_ne_top_of_subset (triadicAdaptiveCell_subset_root z hr J t)
      (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top))]
  exact measureReal_congr (triadicAdaptiveCells_union_ae_eq z hr hI J)

/-- The literal cell weights sum to one, preserving the constant term of the response defect. -/
theorem triadicAdaptiveCells_sum_weights (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) {I : Finset (Fin d)} (hI : I.Nonempty) (J : ℕ) :
    (∑ t ∈ triadicAdaptiveLabels I J,
      volume.real (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d)) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) = 1 := by
  rw [← Finset.sum_div, triadicAdaptiveCells_sum_volume z hr hI J,
    div_self (ne_of_gt (centeredCube_volume_pos z hr))]

/-- A sum over the actual adaptive labels separates retained generations from the unresolved part. -/
theorem triadicAdaptive_sum (I : Finset (Fin d)) (J : ℕ)
    (f : TriadicAdaptiveIndex d J → ℝ) :
    (∑ t ∈ triadicAdaptiveLabels I J, f t) =
      (∑ j : Fin J, ∑ k ∈ triadicRetainedLabels j.val I, f (Sum.inl ⟨j, k⟩)) +
      ∑ k ∈ oddGridUnresolved (triadicHalf J) I, f (Sum.inr k) := by
  classical
  simp only [triadicAdaptiveLabels, Finset.sum_filter, Fintype.sum_sum_type,
    Fintype.sum_sigma]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _
    letI : DecidablePred (fun k : OddGridIndex d (triadicHalf (j.val + 1)) =>
      k ∈ triadicRetainedLabels j.val I) := fun k => Classical.propDecidable _
    exact Finset.sum_ite_mem_eq _ _
  · letI : DecidablePred (fun k : OddGridIndex d (triadicHalf J) =>
      k ∈ oddGridUnresolved (triadicHalf J) I) := fun k => Classical.propDecidable _
    exact Finset.sum_ite_mem_eq _ _

/-- The actual sum of cell weights first retained at generation `J+1` has the geometric bound. -/
theorem triadicRetainedCells_sum_weights_le (hd : 0 < d) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    (∑ k ∈ triadicRetainedLabels J I,
      volume.real (oddGridCell z r hr (triadicHalf (J + 1)) k : Set (SpatialCoordinates d)) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
      (d : ℝ) / (3 : ℝ)^J := by
  rw [← Finset.sum_div, ← oddGrid_subfamily_volume_real]
  exact triadicRetainedRegion_volume_fraction_le hd z hr I J

end SubdiffusiveProcess
