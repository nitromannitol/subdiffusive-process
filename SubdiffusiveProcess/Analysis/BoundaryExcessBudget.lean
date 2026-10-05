module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Combine the five nonnegative coefficients in a boundary excess recurrence. -/
namespace SubdiffusiveProcess

/-- One coefficient pays the error contraction, slope, boundary mean and two forcing terms. -/
theorem boundary_excess_budget (b1 b2 b3 b4 b5 : ℝ)
    (h1 : 0 ≤ b1) (h2 : 0 ≤ b2) (h3 : 0 ≤ b3) (h4 : 0 ≤ b4) (h5 : 0 ≤ b5) :
    ∃ B : ℝ, 0 < B ∧ ∀ A theta eta En Sl Hmean G Hhalf ai ph err Es : ℝ,
      0 ≤ eta → 0 ≤ En → 0 ≤ Sl → 0 ≤ Hmean → 0 ≤ G → 0 ≤ Hhalf →
      0 ≤ ai → 0 ≤ ph → 0 ≤ err →
      Es ≤ (A * theta + b1 * eta) * En + b2 * err * Sl + b3 * err * Hmean +
        b4 * ai * ph * G + b5 * ph * Hhalf →
      Es ≤ (A * theta + B * eta) * En + B * err * Sl +
        B * (err * Hmean + ai * ph * G + ph * Hhalf) := by
  let B := 1 + b1 + b2 + b3 + b4 + b5
  have hB : 0 < B := by dsimp only [B]; linarith only [h1,h2,h3,h4,h5]
  have hb1 : b1 ≤ B := by dsimp only [B]; linarith only [h1,h2,h3,h4,h5]
  have hb2 : b2 ≤ B := by dsimp only [B]; linarith only [h1,h2,h3,h4,h5]
  have hb3 : b3 ≤ B := by dsimp only [B]; linarith only [h1,h2,h3,h4,h5]
  have hb4 : b4 ≤ B := by dsimp only [B]; linarith only [h1,h2,h3,h4,h5]
  have hb5 : b5 ≤ B := by dsimp only [B]; linarith only [h1,h2,h3,h4,h5]
  refine ⟨B, hB, ?_⟩
  intro A theta eta En Sl Hmean G Hhalf ai ph err Es heta hEn hSl hMean hG hH hai hph herr hEs
  have h11 := mul_le_mul_of_nonneg_right hb1 (mul_nonneg heta hEn)
  have h22 := mul_le_mul_of_nonneg_right hb2 (mul_nonneg herr hSl)
  have h33 := mul_le_mul_of_nonneg_right hb3 (mul_nonneg herr hMean)
  have h44 := mul_le_mul_of_nonneg_right hb4 (mul_nonneg (mul_nonneg hai hph) hG)
  have h55 := mul_le_mul_of_nonneg_right hb5 (mul_nonneg hph hH)
  nlinarith only [hEs,h11,h22,h33,h44,h55]

end SubdiffusiveProcess
