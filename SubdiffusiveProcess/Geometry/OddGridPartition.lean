import SubdiffusiveProcess.Geometry.OddGrid
import Mathlib.MeasureTheory.Measure.Real

/-!
# The centered odd grid is an actual Lebesgue partition

Containment and disjointness, together with the exact sum of cell volumes,
prove coverage up to Lebesgue null sets. No partition axiom or floor-function
selection is needed. This concerns Lebesgue volume, not limiting energy or
speed measures.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- Volume is additive on every finite subfamily of these actual disjoint cells. -/
theorem oddGrid_subfamily_volume_real (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (S : Finset (OddGridIndex d m)) :
    volume.real (⋃ k ∈ S, (oddGridCell z r hr m k : Set (SpatialCoordinates d))) =
      ∑ k ∈ S, volume.real (oddGridCell z r hr m k : Set (SpatialCoordinates d)) :=
  measureReal_biUnion_finset
    (fun k _ l _ hkl => oddGridCell_pairwiseDisjoint z hr m hkl)
    (fun k _ => (oddGridCell z r hr m k).isOpen.measurableSet)
    (fun k _ => by rw [oddGridCell_volume]; exact ENNReal.ofReal_ne_top)

/-- The volumes of all children sum to the volume of the actual parent. -/
theorem oddGrid_sum_volume_real (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) :
    (∑ k : OddGridIndex d m, volume.real
      (oddGridCell z r hr m k : Set (SpatialCoordinates d))) = r ^ d := by
  simp_rw [oddGridCell_volume_real]
  simp only [Finset.sum_const, Finset.card_univ, OddGridIndex, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, div_pow]
  field_simp

/-- The union of the disjoint actual open cells has the full parent volume. -/
theorem oddGrid_union_volume_real (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) :
    volume.real (⋃ k : OddGridIndex d m,
      (oddGridCell z r hr m k : Set (SpatialCoordinates d))) = r ^ d := by
  rw [measureReal_iUnion_fintype (oddGridCell_pairwiseDisjoint z hr m)
    (fun k => (oddGridCell z r hr m k).isOpen.measurableSet)
    (fun k => by rw [oddGridCell_volume]; exact ENNReal.ofReal_ne_top)]
  exact oddGrid_sum_volume_real z hr m

/-- The literal open cells partition their parent up to Lebesgue null sets. -/
theorem oddGrid_union_ae_eq (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) :
    (⋃ k : OddGridIndex d m, (oddGridCell z r hr m k : Set (SpatialCoordinates d)))
      =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hsub : (⋃ k : OddGridIndex d m,
      (oddGridCell z r hr m k : Set (SpatialCoordinates d))) ⊆ centeredCube z r hr :=
    iUnion_subset (fun k => oddGridCell_subset z hr m k)
  have hf : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ∞ := by
    rw [centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have he : volume (⋃ k : OddGridIndex d m,
      (oddGridCell z r hr m k : Set (SpatialCoordinates d))) =
      volume (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    apply (measureReal_eq_measureReal_iff (measure_ne_top_of_subset hsub hf) hf).mp
    rw [oddGrid_union_volume_real, centeredCube_volume_real]
  exact ae_eq_of_subset_of_measure_ge hsub he.symm.le
    (isOpen_iUnion (fun k => (oddGridCell z r hr m k).isOpen)).measurableSet.nullMeasurableSet hf

end SubdiffusiveProcess
