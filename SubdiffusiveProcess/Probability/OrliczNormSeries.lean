module

public import SubdiffusiveProcess.Probability.OrliczScalarSeries

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace SubdiffusiveProcess

/-- The imported GMC countable triangle bound controls an actual absolutely convergent norm-valued series. -/
theorem lintegral_exp_sq_norm_tsum_le
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [CompleteSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : ℕ → α → E) (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hsuma : Summable a)
    (hsumF : ∀ᵐ x ∂μ, Summable (fun n => ‖F n x‖))
    (hbound : ∀ n, (∫⁻ x, ENNReal.ofReal
      (Real.exp ((‖F n x‖ / a n) ^ 2)) ∂μ) ≤ 2) :
    (∫⁻ x, ENNReal.ofReal (Real.exp
      ((‖∑' n : ℕ, F n x‖ / (∑' n : ℕ, a n)) ^ 2)) ∂μ) ≤ 2 := by
  have hReal := lintegral_exp_sq_tsum_le μ (fun n x => ‖F n x‖) a
    (fun n => (hF n).norm)
    (fun n => Filter.Eventually.of_forall (fun x => norm_nonneg (F n x)))
    ha hsuma hsumF hbound
  refine (lintegral_mono_ae ?_).trans hReal
  filter_upwards [hsumF] with x hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact (sq_le_sq₀
    (a := ‖∑' n : ℕ, F n x‖ / ∑' n : ℕ, a n)
    (b := (∑' n : ℕ, ‖F n x‖) / ∑' n : ℕ, a n)
    (div_nonneg (norm_nonneg _) (tsum_nonneg fun n => (ha n).le))
    (div_nonneg (tsum_nonneg fun n => norm_nonneg _) (tsum_nonneg fun n => (ha n).le))).2
    (div_le_div_of_nonneg_right (norm_tsum_le_tsum_norm hx)
      (tsum_nonneg fun n => (ha n).le))

end SubdiffusiveProcess
