import SubdiffusiveProcess.Geometry.OddGridPartition

/-!
# The unresolved volume on a centered odd grid

Unresolved labels are precisely those whose actual open cells meet at least
one selected coordinate midplane. Count the middle-coordinate fibers and
use their actual cell volumes. No independence, coefficient estimate, or
assumed geometric remainder enters this argument.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- Labels whose `i`th coordinate is the middle child. -/
def oddGridPlaneCells (m : ℕ) (i : Fin d) : Finset (OddGridIndex d m) :=
  Finset.univ.filter (fun k => (k i).val = m)

/-- Cells unresolved by the selected coordinate midplanes. -/
def oddGridUnresolved (m : ℕ) (I : Finset (Fin d)) : Finset (OddGridIndex d m) :=
  I.biUnion (oddGridPlaneCells m)

/-- The unresolved finite set has its actual geometric meaning. -/
theorem mem_oddGridUnresolved_iff (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (I : Finset (Fin d)) (k : OddGridIndex d m) :
    k ∈ oddGridUnresolved m I ↔ ∃ i ∈ I,
      ∃ x ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d)), x i = z i := by
  simp only [oddGridUnresolved, Finset.mem_biUnion, oddGridPlaneCells,
    Finset.mem_filter, Finset.mem_univ, true_and, oddGridCell_meets_midplane_iff]

/-- Exactly one of the odd coordinate intervals meets a given midplane. -/
theorem oddGridPlaneCells_card (m : ℕ) (i : Fin d) :
    (oddGridPlaneCells m i).card = (2 * m + 1) ^ (d - 1) := by
  let mid : Fin (2 * m + 1) := ⟨m, by omega⟩
  have h := Fintype.card_filter_piFinset_const_eq_of_mem
    (Finset.univ : Finset (Fin (2 * m + 1))) i (Finset.mem_univ mid)
  simpa only [oddGridPlaneCells, Fintype.piFinset_univ, Fin.ext_iff,
    Finset.card_univ, Fintype.card_fin, mid] using h

/-- A union bound on the selected coordinate fibers counts all unresolved cells. -/
theorem oddGridUnresolved_card_le (m : ℕ) (I : Finset (Fin d)) :
    (oddGridUnresolved m I).card ≤ I.card * (2 * m + 1) ^ (d - 1) := by
  unfold oddGridUnresolved
  apply Finset.card_biUnion_le.trans
  simp only [oddGridPlaneCells_card, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, le_refl]

/-- The actual unresolved region occupies at most `card I / (2*m+1)` of parent volume. -/
theorem oddGridUnresolved_volume_real_le (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (m : ℕ) (I : Finset (Fin d)) :
    volume.real (⋃ k ∈ oddGridUnresolved m I,
      (oddGridCell z r hr m k : Set (SpatialCoordinates d))) ≤
      (I.card : ℝ) * r ^ d / (2 * (m : ℝ) + 1) := by
  have hc : ((oddGridUnresolved m I).card : ℝ) ≤
      (I.card : ℝ) * (2 * (m : ℝ) + 1) ^ (d - 1) := by
    exact_mod_cast oddGridUnresolved_card_le m I
  have hp : (2 * (m : ℝ) + 1) ^ d =
      (2 * (m : ℝ) + 1) ^ (d - 1) * (2 * (m : ℝ) + 1) := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  calc
    _ ≤ ∑ k ∈ oddGridUnresolved m I, volume.real
        (oddGridCell z r hr m k : Set (SpatialCoordinates d)) :=
      measureReal_biUnion_finset_le _ _
    _ = ((oddGridUnresolved m I).card : ℝ) *
        (r / (2 * (m : ℝ) + 1)) ^ d := by
      simp only [oddGridCell_volume_real, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((I.card : ℝ) * (2 * (m : ℝ) + 1) ^ (d - 1)) *
        (r / (2 * (m : ℝ) + 1)) ^ d :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      rw [div_pow, hp]
      field_simp

/-- The normalized estimate uses the real volume of the actual root cube. -/
theorem oddGridUnresolved_volume_fraction_le (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (m : ℕ) (I : Finset (Fin d)) :
    volume.real (⋃ k ∈ oddGridUnresolved m I,
      (oddGridCell z r hr m k : Set (SpatialCoordinates d))) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        (I.card : ℝ) / (2 * (m : ℝ) + 1) := by
  apply (div_le_iff₀ (centeredCube_volume_pos z hr)).mpr
  calc
    _ ≤ (I.card : ℝ) * r ^ d / (2 * (m : ℝ) + 1) :=
      oddGridUnresolved_volume_real_le hd z hr m I
    _ = _ := by rw [centeredCube_volume_real]; ring

end SubdiffusiveProcess
