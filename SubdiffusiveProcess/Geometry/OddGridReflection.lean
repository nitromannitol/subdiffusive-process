import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Geometry.CoordinateReflection
import Mathlib.Data.Fin.Rev

/-! # Coordinate reflections permute the actual centered odd grid

Reversing a coordinate label sends `k` to `2*m-k`. The corresponding
geometric map is the same reflection already used on Sobolev functions.
-/
open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
variable {d m : ℕ}

/-- Reverse precisely the selected coordinate labels of an odd grid. -/
def oddGridReflect (I : Finset (Fin d)) (k : OddGridIndex d m) : OddGridIndex d m :=
  fun i => if i ∈ I then (k i).rev else k i

/-- Reversing selected labels twice restores the original grid label. -/
theorem oddGridReflect_involutive (I : Finset (Fin d)) :
    Function.Involutive (oddGridReflect (m := m) I) := by
  intro k
  funext i
  simp only [oddGridReflect]
  split_ifs <;> simp only [Fin.rev_rev]

/-- The reversed coordinate is exactly `2*m-k`, also after coercion to the reals. -/
theorem oddGrid_rev_val_cast (k : Fin (2 * m + 1)) :
    ((k.rev).val : ℝ) = 2 * (m : ℝ) - (k.val : ℝ) := by
  have hk : k.val ≤ 2 * m := Nat.le_of_lt_succ k.isLt
  have he : k.rev.val = 2 * m - k.val := by
    rw [Fin.val_rev]
    omega
  rw [he, Nat.cast_sub hk, Nat.cast_mul, Nat.cast_ofNat]

/-- The reflected center is the center at the explicitly reversed grid label. -/
theorem coordinateReflection_oddGridCenter (z : SpatialCoordinates d) (r : ℝ)
    (I : Finset (Fin d)) (k : OddGridIndex d m) :
    coordinateReflection z I (oddGridCenter z r m k) =
      oddGridCenter z r m (oddGridReflect I k) := by
  funext i
  by_cases hi : i ∈ I
  · simp only [coordinateReflection, oddGridCenter, oddGridReflect, hi, if_pos,
      oddGrid_rev_val_cast]
    ring
  · simp only [coordinateReflection, oddGridCenter, oddGridReflect, hi, if_false]

/-- The exact domain preimage needed for the Sobolev response covariance. -/
theorem coordinateReflection_preimage_oddGridCell (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (I : Finset (Fin d)) (k : OddGridIndex d m) :
    coordinateReflection z I ⁻¹'
      (oddGridCell z r hr m (oddGridReflect I k) : Set (SpatialCoordinates d)) =
      (oddGridCell z r hr m k : Set (SpatialCoordinates d)) := by
  unfold oddGridCell
  rw [← coordinateReflection_oddGridCenter]
  exact coordinateReflection_preimage_cube z I _ _

/-- The actual cell image is another cell of the same original grid. -/
theorem coordinateReflection_image_oddGridCell (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (I : Finset (Fin d)) (k : OddGridIndex d m) :
    coordinateReflection z I '' (oddGridCell z r hr m k : Set (SpatialCoordinates d)) =
      (oddGridCell z r hr m (oddGridReflect I k) : Set (SpatialCoordinates d)) := by
  rw [← coordinateReflection_preimage_oddGridCell z hr I k]
  exact (coordinateReflection_involutive z I).surjective.image_preimage _

end SubdiffusiveProcess
