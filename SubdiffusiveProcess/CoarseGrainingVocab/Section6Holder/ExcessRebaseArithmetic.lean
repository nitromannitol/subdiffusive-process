module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.CampanatoRebaseArithmetic

@[expose] public section

/-!
# Hölder Step 7: bounded-window excess arithmetic

On the Step-7 range `m-n ≤ (1-alpha)⁻¹`, the linear stopping
exponential is dimension-only.  The fixed iteration contraction is exactly
the printed quarter-power decay.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

noncomputable section

/-- The linear stopping exponential is uniformly bounded on the Step-7
window. -/
theorem holderExcess_exponential_le {C C₁ alpha gap : ℝ}
    (hC₁ : 0 < C₁) (hC : 0 ≤ C) (halpha : alpha ≤ 1)
    (hwindow : gap ≤ (1 - alpha)⁻¹) :
    Real.exp (C * (C₁⁻¹ * (1 - alpha)) * gap) ≤ Real.exp (C * C₁⁻¹) := by
  have ha : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha
  by_cases ha0 : 1 - alpha = 0
  · rw [ha0]
    simp only [mul_zero, zero_mul, Real.exp_zero]
    exact (Real.one_le_exp_iff.mpr (mul_nonneg hC (inv_nonneg.mpr hC₁.le)))
  · have haPos : 0 < 1 - alpha := lt_of_le_of_ne ha (Ne.symm ha0)
    have hmul : (1 - alpha) * gap ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hwindow ha
      rw [mul_inv_cancel₀ ha0] at this
      exact this
    apply Real.exp_le_exp.mpr
    have hnonneg : 0 ≤ C * C₁⁻¹ := mul_nonneg hC (inv_nonneg.mpr hC₁.le)
    nlinarith

/-- The chosen contraction `theta = 3⁻¹/⁴` gives the literal printed
decay at every real scale gap. -/
theorem holderTheta_rpow_eq (gap : ℝ) :
    ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ gap = (3 : ℝ) ^ (-gap / 4) := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- Integer-scale specialization used by the applied iteration theorem. -/
theorem holderTheta_zpow_eq {n ell : ℤ} :
    ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ (ell - n) =
      (3 : ℝ) ^ (-(((ell : ℝ) - (n : ℝ)) / 4)) := by
  rw [← Real.rpow_intCast, holderTheta_rpow_eq]
  congr 1
  push_cast
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
