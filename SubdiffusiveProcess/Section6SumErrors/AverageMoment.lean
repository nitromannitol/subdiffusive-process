import SubdiffusiveProcess.Section6SumErrors.WindowBounds
/-!
# AverageMoment

A Gaussian window carrier controls the expectation-form bound for an average with enlarged deterministic mean and fluctuation coefficients.
-/

namespace SubdiffusiveProcess.Section6SumErrors
open MeasureTheory Homogenization IndependentSums
open scoped ENNReal
noncomputable section

theorem lintegral_average_exp_square_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S F : Ω → ℝ}
    {W a a₀ V B : ℝ} (hW : 0 < W) (hV : 0 < V) (hB : 0 < B)
    (hm : AEMeasurable F μ) (hF : IsBigO μ (gammaSigma 2) F V)
    (hS : ∀ᵐ ω ∂μ, S ω ≤ a₀ + F ω)
    (ha : a₀ ≤ W * a) (hscale : 2 * V ≤ B * W) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
      ((B⁻¹ * max (S ω / W - a) 0) ^ (2 : ℕ))) ∂μ ≤ 2 := by
  apply le_trans _ (lintegral_exp_square_le_of_isBigO hV hm hF)
  apply lintegral_mono_ae
  filter_upwards [hS] with ω hω
  let x := max (S ω / W - a) 0
  let y := max (F ω) 0
  have hx : 0 ≤ x := le_max_right _ _
  have hy : 0 ≤ y := le_max_right _ _
  have hxy : x * W ≤ y := by
    have hfy : F ω ≤ y := le_max_left _ _
    have hs : S ω ≤ W * a + y := by linarith
    have h : S ω / W - a ≤ y / W := by
      rw [sub_le_iff_le_add, div_le_iff₀ hW]
      have heq : (y / W + a) * W = y + a * W := by field_simp
      rw [heq]
      linarith
    have hmax : x ≤ y / W := max_le h (div_nonneg hy hW.le)
    exact (le_div_iff₀ hW).mp hmax
  have hscaled : B⁻¹ * x ≤ (2 * V)⁻¹ * y := by
    rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ hB (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right hscale hx
    have h2 := mul_le_mul_of_nonneg_left hxy hB.le
    nlinarith
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    ((sq_le_sq₀ (mul_nonneg (inv_nonneg.mpr hB.le) hx)
      (mul_nonneg (inv_nonneg.mpr (by positivity)) hy)).mpr hscaled))

end
end SubdiffusiveProcess.Section6SumErrors
