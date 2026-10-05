module

public import Mathlib
public import SubdiffusiveProcess.Model.OGammaLE

@[expose] public section

/-! Two-sided expectation control and its absolute Gaussian moment. -/
open MeasureTheory
noncomputable section
namespace SubdiffusiveProcess.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma exp_abs_normalized_sq_eq (σ x : ℝ) :
    Real.exp ((σ⁻¹ * |x|) ^ (2 : ℕ)) =
      Real.exp ((σ⁻¹ * max x 0) ^ (2 : ℝ)) +
        Real.exp ((σ⁻¹ * max (-x) 0) ^ (2 : ℝ)) - 1 := by
  by_cases hx : 0 ≤ x
  · simp only [abs_of_nonneg hx, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx),
      mul_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0), Real.exp_zero,
      Real.rpow_two, add_sub_cancel_right]
  · have hn : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
    simp only [abs_of_nonpos (le_of_not_ge hx), max_eq_right (le_of_not_ge hx),
      max_eq_left hn, mul_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
      Real.exp_zero, Real.rpow_two]
    ring

lemma integrable_exp_abs_normalized_sq {σ : ℝ} {X : Ω → ℝ}
    (hp : SubdiffusiveProcess.OGammaLE μ 2 σ X) (hn : SubdiffusiveProcess.OGammaLE μ 2 σ (fun ω => -X ω)) :
    Integrable (fun ω => Real.exp ((σ⁻¹ * |X ω|) ^ (2 : ℕ))) μ := by
  have h := (hp.1.add hn.1).sub (integrable_const (1 : ℝ))
  exact h.congr (Filter.Eventually.of_forall fun ω =>
    (exp_abs_normalized_sq_eq σ (X ω)).symm)

lemma integral_exp_abs_normalized_sq_le {σ : ℝ} {X : Ω → ℝ}
    (hp : SubdiffusiveProcess.OGammaLE μ 2 σ X) (hn : SubdiffusiveProcess.OGammaLE μ 2 σ (fun ω => -X ω)) :
    ∫ ω, Real.exp ((σ⁻¹ * |X ω|) ^ (2 : ℕ)) ∂μ ≤ 4 := by
  simp_rw [exp_abs_normalized_sq_eq]
  have hsum : Integrable (fun ω => Real.exp ((σ⁻¹ * max (X ω) 0) ^ (2 : ℝ)) +
      Real.exp ((σ⁻¹ * max (-X ω) 0) ^ (2 : ℝ))) μ := hp.1.add hn.1
  rw [integral_sub hsum (integrable_const (1 : ℝ)), integral_add hp.1 hn.1]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  linarith [hp.2, hn.2]

lemma aemeasurable_abs_of_ogamma_two {σ : ℝ} (hσ : 0 < σ) {X : Ω → ℝ}
    (hp : SubdiffusiveProcess.OGammaLE μ 2 σ X) (hn : SubdiffusiveProcess.OGammaLE μ 2 σ (fun ω => -X ω)) :
    AEMeasurable (fun ω => |X ω|) μ := by
  have h := ((integrable_exp_abs_normalized_sq hp hn).aemeasurable.log.sqrt).const_mul σ
  convert h using 1
  ext ω
  rw [Real.log_exp, Real.sqrt_sq (mul_nonneg (inv_nonneg.mpr hσ.le) (abs_nonneg _))]
  field_simp

lemma lintegral_exp_abs_normalized_sq_le {σ : ℝ} {X : Ω → ℝ}
    (hp : SubdiffusiveProcess.OGammaLE μ 2 σ X) (hn : SubdiffusiveProcess.OGammaLE μ 2 σ (fun ω => -X ω)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((σ⁻¹ * |X ω|) ^ (2 : ℕ))) ∂μ ≤ 4 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_abs_normalized_sq hp hn)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  exact (ENNReal.ofReal_le_ofReal (integral_exp_abs_normalized_sq_le hp hn)).trans_eq
    (by norm_num)

end SubdiffusiveProcess.Probability
