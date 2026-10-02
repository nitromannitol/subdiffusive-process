import SubdiffusiveProcess.Probability.SeriesMoment
import Homogenization.Probability.IndependentSums.GammaSigma.Basic

/-! # Real moment readout and geometric absorption for cell envelopes -/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Exact real integral readout of a finite nonnegative moment. -/
theorem eLpNorm_nonneg_eq_ofReal_integral_root {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (f : Ω → ℝ) (hf : ∀ omega, 0 ≤ f omega) {q : ℝ} (hq : 0 < q)
    (hi : Integrable (fun omega => f omega ^ q) mu) :
    eLpNorm f (ENNReal.ofReal q) mu =
      ENNReal.ofReal ((∫ omega, f omega ^ q ∂mu) ^ q⁻¹) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by simpa using hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le, one_div]
  have hfun : (fun omega => ‖f omega‖ₑ ^ q) =
      fun omega => ENNReal.ofReal (f omega ^ q) := by
    funext omega
    rw [Real.enorm_eq_ofReal (hf omega), ENNReal.ofReal_rpow_of_nonneg (hf omega) hq.le]
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hf omega) q),
    ← ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun omega => Real.rpow_nonneg (hf omega) q)
      (inv_nonneg.mpr hq.le)]

/-- Any fixed positive geometric margin absorbs a linear scale factor. -/
theorem linear_mul_exp_le_geometric {A c t : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (ht : 0 ≤ t) :
    1 + A * t * Real.exp (c * t) ≤
      (1 + A * c⁻¹) * Real.exp (2 * c * t) := by
  have hx := Real.add_one_le_exp (c * t)
  have htbound : t ≤ c⁻¹ * Real.exp (c * t) := by
    have h : c * t ≤ Real.exp (c * t) := by linarith
    have hmul := mul_le_mul_of_nonneg_left h (inv_pos.mpr hc).le
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hmul
  have hone : 1 ≤ Real.exp (2 * c * t) := Real.one_le_exp (by positivity)
  calc
    _ ≤ 1 + A * (c⁻¹ * Real.exp (c * t)) * Real.exp (c * t) := by gcongr
    _ = 1 + A * c⁻¹ * Real.exp (2 * c * t) := by
      rw [show 2 * c * t = c * t + c * t by ring, Real.exp_add]
      ring
    _ ≤ _ := by nlinarith

end SubdiffusiveProcess.Static
