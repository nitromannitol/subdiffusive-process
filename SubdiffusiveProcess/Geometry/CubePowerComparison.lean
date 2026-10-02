import SubdiffusiveProcess.Geometry.Cube

/-! Containment compares cube side lengths and permits weakening a positive-radius power estimate.
No regularity or energy bound is assumed here. -/
open MeasureTheory Set
noncomputable section
namespace SubdiffusiveProcess

/-- A contained positive cube has side no larger than its ambient cube. -/
theorem cube_side_le_of_subset {d : ℕ} [NeZero d]
    (z w : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hsub : Metric.ball w (r / 2) ⊆ Metric.ball z (R / 2)) : r ≤ R := by
  have hvol : volume (centeredCube w r hr : Set (SpatialCoordinates d)) ≤
      volume (centeredCube z R hR : Set (SpatialCoordinates d)) := measure_mono hsub
  rw [centeredCube_volume w hr, centeredCube_volume z hR] at hvol
  have hpow : r ^ d ≤ R ^ d := by
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    simpa only [ENNReal.toReal_ofReal (pow_nonneg hr.le d),
      ENNReal.toReal_ofReal (pow_nonneg hR.le d)] using hreal
  exact (pow_le_pow_iff_left₀ hr.le hR.le (NeZero.ne d)).mp hpow

/-- The ambient side controls the loss when decreasing a radius exponent on any contained cube. -/
theorem cube_rpow_exponent_le {d : ℕ} [NeZero d]
    (z w : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hsub : Metric.ball w (r / 2) ⊆ Metric.ball z (R / 2))
    (s t : ℝ) (hts : t ≤ s) : r ^ s ≤ R ^ (s - t) * r ^ t := by
  have hside := cube_side_le_of_subset z w R r hR hr hsub
  calc
    r ^ s = r ^ (s - t) * r ^ t := by rw [← Real.rpow_add hr, sub_add_cancel]
    _ ≤ R ^ (s - t) * r ^ t := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hr.le hside (sub_nonneg.mpr hts)) (Real.rpow_nonneg hr.le t)

end SubdiffusiveProcess
