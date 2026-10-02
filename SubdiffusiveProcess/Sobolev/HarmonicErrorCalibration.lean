import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scalar calibration for the harmonic comparison window.
The chosen bound precedes the accuracy parameter; no analytic estimate is asserted here.
-/

namespace SubdiffusiveProcess

/-- Enlarging the deterministic constant enlarges its exponential scale factor. -/
theorem exponential_scale_factor_mono {C D t : ℝ}
    (hC : 0 ≤ C) (hCD : C ≤ D) (ht : 0 ≤ t) :
    C * (3 : ℝ) ^ (C * t) ≤ D * (3 : ℝ) ^ (D * t) := by
  exact mul_le_mul hCD
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hCD ht))
    (Real.rpow_nonneg (by norm_num) _) (hC.trans hCD)

/-- The exponential scale factor dominates its nonnegative base constant. -/
theorem le_exponential_scale_factor {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) :
    C ≤ C * (3 : ℝ) ^ (C * t) := by
  exact le_mul_of_one_le_right hC (Real.one_le_rpow (by norm_num) (mul_nonneg hC ht))

/-- A bound chosen before the accuracy parameter gives a strict harmonic window and the desired error coefficient. -/
theorem harmonic_error_calibration
    {C Charm E0 epshom cdet err : ℝ}
    (hC : 1 ≤ C) (hCharm : 0 ≤ Charm) (hCharmC : Charm ≤ C)
    (hE0 : 0 < E0) (hEC : 2 / E0 ≤ C)
    (heps : 0 < epshom) (heps1 : epshom ≤ 1)
    (hcdet : cdet ≤ C⁻¹) (herr : err ≤ epshom * cdet) :
    err < E0 ∧ Charm * err ≤ epshom := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hinvE : C⁻¹ ≤ E0 / 2 := by
    have htwo : 2 ≤ C * E0 := (div_le_iff₀ hE0).mp hEC
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hCpos).mpr
    nlinarith only [htwo]
  have hsmall : err ≤ C⁻¹ := by
    calc
      err ≤ epshom * cdet := herr
      _ ≤ epshom * C⁻¹ := mul_le_mul_of_nonneg_left hcdet heps.le
      _ ≤ 1 * C⁻¹ := mul_le_mul_of_nonneg_right heps1 (inv_nonneg.mpr hCpos.le)
      _ = C⁻¹ := one_mul _
  have hcoeff : Charm * C⁻¹ ≤ 1 := by
    calc
      Charm * C⁻¹ ≤ C * C⁻¹ := mul_le_mul_of_nonneg_right hCharmC (inv_nonneg.mpr hCpos.le)
      _ = 1 := mul_inv_cancel₀ hCpos.ne'
  refine ⟨lt_of_le_of_lt (hsmall.trans hinvE) (by linarith only [hE0]), ?_⟩
  calc
    Charm * err ≤ Charm * (epshom * cdet) := mul_le_mul_of_nonneg_left herr hCharm
    _ ≤ Charm * (epshom * C⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcdet heps.le) hCharm
    _ = epshom * (Charm * C⁻¹) := by ring
    _ ≤ epshom * 1 := mul_le_mul_of_nonneg_left hcoeff heps.le
    _ = epshom := mul_one _

end SubdiffusiveProcess
