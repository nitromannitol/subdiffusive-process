module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

@[expose] public section

/-! First-moment upper-tail bounds for real random variables. The estimates
use outer measures and make no sign assumption on the random variable.
-/
open MeasureTheory Set
open scoped ENNReal
namespace SubdiffusiveProcess

/-- A first absolute moment bounds the strict upper tail at a positive level. -/
theorem measure_gt_le_of_first_moment {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (f : Omega → ℝ) (hf : AEStronglyMeasurable f mu)
    (eps B : ℝ) (heps : 0 < eps) (hB : 0 ≤ B)
    (hbound : eLpNorm f 1 mu ≤ ENNReal.ofReal B) :
    mu {omega | eps < f omega} ≤ ENNReal.ofReal (B / eps) := by
  have htail := meas_ge_le_mul_pow_eLpNorm_enorm mu
    (p := 1) (f := f) one_ne_zero ENNReal.one_ne_top
    (ENNReal.ofReal_pos.mpr heps).ne'
    (fun h => (ENNReal.ofReal_ne_top h).elim)
  simp only [ENNReal.toReal_one, ENNReal.rpow_one] at htail
  have hsub : {omega | eps < f omega} ⊆ {omega | ENNReal.ofReal eps ≤ ‖f omega‖ₑ} := by
    intro omega homega
    change ENNReal.ofReal eps ≤ ‖f omega‖ₑ
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (homega.le.trans (le_abs_self _))
  refine (measure_mono hsub).trans (htail.trans ?_)
  calc (ENNReal.ofReal eps)⁻¹ * eLpNorm f 1 mu ≤
      (ENNReal.ofReal eps)⁻¹ * ENNReal.ofReal B := mul_le_mul_right hbound _
    _ = ENNReal.ofReal (B / eps) := by
      rw [mul_comm, ← div_eq_mul_inv, ENNReal.ofReal_div_of_pos heps]

end SubdiffusiveProcess
