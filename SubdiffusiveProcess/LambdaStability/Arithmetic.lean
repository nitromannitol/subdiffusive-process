module

public import SubdiffusiveProcess.LambdaStability.WeightedSum

@[expose] public section

/-! Absorbing the one-scale factors into a dimension-only constant. -/
noncomputable section
namespace SubdiffusiveProcess.LambdaStability

def stabilityConstant (d : ℕ) : ℝ := 36 * (d : ℝ) + 3 * Real.sqrt (12 * (d : ℝ)) + 1

theorem stabilityConstant_pos (d : ℕ) : 0 < stabilityConstant d := by
  unfold stabilityConstant
  positivity

theorem matrix_stability_arithmetic (d : ℕ) {s I E : ℝ}
    (hs : s < 1 / 2) (hI : 0 ≤ I) (hE : 0 ≤ E) :
    I * (12 * (d : ℝ) / (1 - 2 * s)) * ((3 : ℝ) ^ (2 * s) * E) ≤
      stabilityConstant d / (1 - 2 * s) * I * E := by
  have hden : 0 < 1 - 2 * s := by linarith only [hs]
  have hfac : 0 ≤ 12 * (d : ℝ) / (1 - 2 * s) := by positivity
  have hpow : (3 : ℝ) ^ (2 * s) ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith only [hs] : 2 * s ≤ 1)
  have hC : 36 * (d : ℝ) ≤ stabilityConstant d := by
    unfold stabilityConstant
    linarith only [Real.sqrt_nonneg (12 * (d : ℝ))]
  calc
    I * (12 * (d : ℝ) / (1 - 2 * s)) * ((3 : ℝ) ^ (2 * s) * E) ≤
        I * (12 * (d : ℝ) / (1 - 2 * s)) * (3 * E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hE) (mul_nonneg hI hfac)
    _ = (36 * (d : ℝ) / (1 - 2 * s)) * I * E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hC hden.le) hI) hE

theorem error_stability_arithmetic (d : ℕ) {s t E : ℝ}
    (hs : s < 1 / 2) (hE : 0 ≤ E) :
    Real.sqrt (12 * (d : ℝ) / (1 - 2 * s) * (t / (t - s))) * ((3 : ℝ) ^ s * E) ≤
      stabilityConstant d / Real.sqrt (1 - 2 * s) * Real.sqrt (t / (t - s)) * E := by
  have hden : 0 < 1 - 2 * s := by linarith only [hs]
  have hpow : (3 : ℝ) ^ s ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith only [hs] : s ≤ 1)
  have hC : 3 * Real.sqrt (12 * (d : ℝ)) ≤ stabilityConstant d := by
    unfold stabilityConstant
    linarith only [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))]
  have hnum : 0 ≤ 12 * (d : ℝ) := by positivity
  have hsqrt : Real.sqrt (12 * (d : ℝ) / (1 - 2 * s) * (t / (t - s))) =
      Real.sqrt (12 * (d : ℝ)) / Real.sqrt (1 - 2 * s) * Real.sqrt (t / (t - s)) := by
    rw [Real.sqrt_mul (div_nonneg hnum hden.le), Real.sqrt_div hnum]
  rw [hsqrt]
  have hfac : 0 ≤ Real.sqrt (12 * (d : ℝ)) / Real.sqrt (1 - 2 * s) *
      Real.sqrt (t / (t - s)) := by positivity
  calc
    (Real.sqrt (12 * (d : ℝ)) / Real.sqrt (1 - 2 * s) * Real.sqrt (t / (t - s))) *
        ((3 : ℝ) ^ s * E) ≤
        (Real.sqrt (12 * (d : ℝ)) / Real.sqrt (1 - 2 * s) * Real.sqrt (t / (t - s))) * (3 * E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hE) hfac
    _ = (3 * Real.sqrt (12 * (d : ℝ))) / Real.sqrt (1 - 2 * s) *
        Real.sqrt (t / (t - s)) * E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hC (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) hE

end SubdiffusiveProcess.LambdaStability
