module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalCarrierGoodEventPrices

@[expose] public section

/-!
# Explicit aggregation of the physical-carrier profile budgets

This is the final scalar bookkeeping after the canonical-radius iteration.
It collects the two copies of the affine-mode energy and the externalized
fine-datum energy without changing any of the scale-dependent carriers.

 this is the constant collection at the end of
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryAssemblyEnergy.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

/-- Collect the literal physical-carrier coefficients into four nonnegative
parent budgets.  In particular, the affine budget has coefficient `183/8`
and no inverse-gap or inverse-fractional-order factor. -/
theorem boundaryPhysicalCarrier_profile_le_fourBudgets
    {C K Av Aell BE Ag P A H G X : ℝ}
    (hC : 0 < C) (hK : 0 < K)
    (hAvA : Av ≤ A) (hAellA : Aell ≤ A)
    (hBEH : BE ≤ H) (hAgG : Ag ≤ G)
    (hXP : X ≤ P) :
    ((79 / 8 : ℝ) * Av + (57 / 8 : ℝ) * BE +
          4 * (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE + 13 * Aell +
          3 * Ag + 4 * X) * boundaryThreeQuarterRadiusIterationConst ≤
      ((183 / 8 : ℝ) * A +
          (61 / 8 + 4 * (64 * C ^ 4 * K)⁻¹) * H +
          3 * G + 4 * P) * boundaryThreeQuarterRadiusIterationConst := by
  have hden : 0 < 64 * C ^ 4 * K := by positivity
  have hinv : 0 ≤ (64 * C ^ 4 * K)⁻¹ := (inv_pos.mpr hden).le
  have hR : 0 ≤ boundaryThreeQuarterRadiusIterationConst :=
    boundaryThreeQuarterRadiusIterationConst_nonneg
  apply mul_le_mul_of_nonneg_right _ hR
  have h1 := mul_le_mul_of_nonneg_left hAvA (by norm_num : (0 : ℝ) ≤ 79 / 8)
  have h2 := mul_le_mul_of_nonneg_left hAellA (by norm_num : (0 : ℝ) ≤ 13)
  have h3 := mul_le_mul_of_nonneg_left hBEH
    (by positivity : (0 : ℝ) ≤ 57 / 8 + 4 * (1 / 8 + (64 * C ^ 4 * K)⁻¹))
  have h4 := mul_le_mul_of_nonneg_left hAgG (by norm_num : (0 : ℝ) ≤ 3)
  have h5 := mul_le_mul_of_nonneg_left hXP (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith only [h1, h2, h3, h4, h5]

/-- Compose the explicit physical-carrier radius row with the four parent
budgets.  This is the complete finite-profile bookkeeping step: all analytic
information is confined to the five displayed budget comparisons. -/
theorem boundaryPhysicalCarrier_profile_le_fourBudgets_of_raw
    {C K Av Aell BE Ag P A H G X E : ℝ}
    (hC : 0 < C) (hK : 0 < K)
    (hraw : E ≤
      ((79 / 8 : ℝ) * Av + (57 / 8 : ℝ) * BE +
          4 * (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE + 13 * Aell +
          3 * Ag + 4 * X) * boundaryThreeQuarterRadiusIterationConst)
    (hAvA : Av ≤ A) (hAellA : Aell ≤ A)
    (hBEH : BE ≤ H) (hAgG : Ag ≤ G) (hXP : X ≤ P) :
    E ≤
      ((183 / 8 : ℝ) * A +
          (61 / 8 + 4 * (64 * C ^ 4 * K)⁻¹) * H +
          3 * G + 4 * P) * boundaryThreeQuarterRadiusIterationConst := by
  exact hraw.trans
    (boundaryPhysicalCarrier_profile_le_fourBudgets hC hK hAvA hAellA
      hBEH hAgG hXP)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
