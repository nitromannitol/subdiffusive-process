import SubdiffusiveProcess.Sobolev.WeakGradient
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Actual open coordinate cubes

`SpatialCoordinates d` carries the maximum norm, so its open ball of radius
`r / 2` is precisely the axis-aligned cube of side `r`. The energy still uses
the Euclidean coordinate pairing. Keeping these conventions separate avoids
replacing the unit slopes of the response defect by maximum-norm unit slopes.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- The open coordinate cube of positive side length `r` centered at `z`. -/
def centeredCube (z : SpatialCoordinates d) (r : ℝ) (_hr : 0 < r) :
    Opens (SpatialCoordinates d) := ⟨Metric.ball z (r / 2), Metric.isOpen_ball⟩

/-- The metric definition agrees with the literal product of open coordinate intervals. -/
theorem centeredCube_eq_pi (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun i => Set.Ioo (z i - r / 2) (z i + r / 2)) := by
  change Metric.ball z (r / 2) = _
  rw [ball_pi z (half_pos hr)]
  simp only [Real.ball_eq_Ioo]

/-- Cubes provide the bounded domains needed by actual affine Sobolev data. -/
theorem centeredCube_isBounded (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Bornology.IsBounded (centeredCube z r hr : Set (SpatialCoordinates d)) :=
  Metric.isBounded_ball

/-- The exact Lebesgue volume uses the side length, not the radius. -/
theorem centeredCube_volume (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    volume (centeredCube z r hr : Set (SpatialCoordinates d)) = ENNReal.ofReal (r ^ d) := by
  change volume (Metric.ball z (r / 2)) = _
  rw [Real.volume_pi_ball z (half_pos hr)]
  simp [mul_div_cancel₀]

instance centeredCube_isFiniteMeasure (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    IsFiniteMeasure (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
  isFiniteMeasure_restrict.mpr (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top)

/-- Real-valued volume of the cube is exactly the `d`th power of its side. -/
theorem centeredCube_volume_real (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = r ^ d := by
  rw [Measure.real, centeredCube_volume, ENNReal.toReal_ofReal (pow_nonneg hr.le _)]

/-- The normalization denominator is strictly positive, including dimension zero. -/
theorem centeredCube_volume_pos (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [centeredCube_volume_real]
  exact pow_pos hr _

end SubdiffusiveProcess
