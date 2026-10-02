import SubdiffusiveProcess.Geometry.OddGridReflection
import SubdiffusiveProcess.Geometry.OddGridResidual
import SubdiffusiveProcess.Geometry.CoordinateFold

/-! # The fold on a cell avoiding the active planes

The side of a noncentral coordinate interval is constant throughout that
interval. Consequently a single, explicitly selected coordinate reflection
agrees with the fold on the whole retained open cell.
-/
open Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
variable {d m : ℕ}

/-- A cell avoids the active planes exactly when its active coordinate labels are noncentral. -/
theorem not_mem_oddGridUnresolved_iff (I : Finset (Fin d)) (k : OddGridIndex d m) :
    k ∉ oddGridUnresolved m I ↔ ∀ i ∈ I, (k i).val ≠ m := by
  simp only [oddGridUnresolved, Finset.mem_biUnion, oddGridPlaneCells,
    Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]

/-- Every point of a cell with a smaller label lies strictly below the root midplane. -/
theorem oddGridCell_coord_lt_center (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (k : OddGridIndex d m) {x : SpatialCoordinates d}
    (hx : x ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d)))
    {i : Fin d} (hk : (k i).val < m) : x i < z i := by
  have hi := (mem_oddGridCell z hr m k x).mp hx i
  let h := r / (2 * (m : ℝ) + 1)
  have hh : 0 < h := div_pos hr (by positivity)
  have hstep : ((k i).val : ℝ) + 1 ≤ (m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hk
  change z i + ((k i).val - (m : ℝ)) * h - h / 2 < x i ∧
    x i < z i + ((k i).val - (m : ℝ)) * h + h / 2 at hi
  nlinarith [mul_le_mul_of_nonneg_right hstep hh.le]

/-- Every point of a cell with a larger label lies strictly above the root midplane. -/
theorem oddGridCell_center_lt_coord (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (k : OddGridIndex d m) {x : SpatialCoordinates d}
    (hx : x ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d)))
    {i : Fin d} (hk : m < (k i).val) : z i < x i := by
  have hi := (mem_oddGridCell z hr m k x).mp hx i
  let h := r / (2 * (m : ℝ) + 1)
  have hh : 0 < h := div_pos hr (by positivity)
  have hstep : (m : ℝ) + 1 ≤ ((k i).val : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hk
  change z i + ((k i).val - (m : ℝ)) * h - h / 2 < x i ∧
    x i < z i + ((k i).val - (m : ℝ)) * h + h / 2 at hi
  nlinarith [mul_le_mul_of_nonneg_right hstep hh.le]

/-- Active coordinates whose cell center lies on the wrong prescribed side. -/
def oddGridFoldReflections (I P : Finset (Fin d)) (k : OddGridIndex d m) : Finset (Fin d) :=
  I.filter (fun i => if i ∈ P then m < (k i).val else (k i).val < m)

/-- On an actual cell avoiding every active plane, the fold equals one affine reflection. -/
theorem coordinateFold_eqOn_oddGridCell (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (I P : Finset (Fin d)) (k : OddGridIndex d m) (hk : k ∉ oddGridUnresolved m I) :
    EqOn (coordinateFold z I P) (coordinateReflection z (oddGridFoldReflections I P k))
      (oddGridCell z r hr m k : Set (SpatialCoordinates d)) := by
  intro x hx
  funext i
  by_cases hi : i ∈ I
  · have hki := (not_mem_oddGridUnresolved_iff I k).mp hk i hi
    rcases lt_or_gt_of_ne hki with hl | hl
    · have hxz := oddGridCell_coord_lt_center z hr k hx hl
      have hnl : ¬ m < (k i).val := not_lt_of_ge hl.le
      by_cases hp : i ∈ P <;>
        simp only [coordinateFold, coordinateReflection, oddGridFoldReflections,
          Finset.mem_filter, coordinateReflectionSign, hi, hp, hl, hnl, if_true, if_false,
          and_true, and_false, abs_of_nonpos (sub_nonpos.mpr hxz.le)] <;> ring
    · have hxz := oddGridCell_center_lt_coord z hr k hx hl
      have hnl : ¬ (k i).val < m := not_lt_of_ge hl.le
      by_cases hp : i ∈ P <;>
        simp only [coordinateFold, coordinateReflection, oddGridFoldReflections,
          Finset.mem_filter, coordinateReflectionSign, hi, hp, hl, hnl, if_true, if_false,
          and_true, and_false, abs_of_nonneg (sub_nonneg.mpr hxz.le)] <;> ring
  · simp only [coordinateFold, coordinateReflection, oddGridFoldReflections,
      Finset.mem_filter, hi, false_and, if_false]

/-- The fold's actual retained-cell image is the explicitly identified original-grid cell. -/
theorem coordinateFold_image_oddGridCell (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (I P : Finset (Fin d)) (k : OddGridIndex d m) (hk : k ∉ oddGridUnresolved m I) :
    coordinateFold z I P '' (oddGridCell z r hr m k : Set (SpatialCoordinates d)) =
      (oddGridCell z r hr m (oddGridReflect (oddGridFoldReflections I P k) k) :
        Set (SpatialCoordinates d)) := by
  rw [Set.image_congr (coordinateFold_eqOn_oddGridCell z hr I P k hk)]
  exact coordinateReflection_image_oddGridCell z hr _ k

end SubdiffusiveProcess
