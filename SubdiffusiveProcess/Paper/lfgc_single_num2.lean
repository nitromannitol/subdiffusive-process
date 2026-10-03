module

public import SubdiffusiveProcess.Paper.lfgc_single_parts

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Disorder thresholds for the single-point cover
-/

open Real

namespace Paper
/-- A threshold making `C = 2εd/(27(1+d)δ)` satisfy `C² ≥ Λ`. -/
theorem aux_lfgc_single_num2_cell_const_ge {ε Λ δ : ℝ} {d : ℕ} (hd : 0 < d) (hε : 0 < ε) (hΛ : 0 < Λ) (hδ : 0 < δ)
    (hδle : δ ≤ 2 * ε * d / (27 * (1 + d) * Real.sqrt Λ)) :
    Λ ≤ (2 * ε * d / 27 / ((1 + d) * δ)) ^ 2 := by
  have hs : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr hΛ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : Real.sqrt Λ ≤ 2 * ε * d / 27 / ((1 + d) * δ) := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hδle
    nlinarith
  calc Λ = Real.sqrt Λ ^ 2 := (Real.sq_sqrt hΛ.le).symm
    _ ≤ _ := pow_le_pow_left₀ hs.le h1 2

theorem aux_lfgc_single_num2_exp_neg_le_inv_of_log_le {x C : ℝ} (hx : 0 ≤ x) (h : Real.log x ≤ C) :
    x * Real.exp (-C) ≤ 1 := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0]; simp
  · have : Real.exp (-C) ≤ Real.exp (-Real.log x) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg (Real.log x), Real.exp_log hpos] at this
    calc x * Real.exp (-C) ≤ x * x⁻¹ := mul_le_mul_of_nonneg_left this hx
      _ = 1 := mul_inv_cancel₀ hpos.ne'

/-- The bad-event numeric: `e^{-(R+1)(H+1)}/(8(1-e^{-(R+1)})) ≤ e^{-R H}/8`. -/
theorem lfgc_single_num2 {R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) :
    Real.exp (-(R + 1) * (H + 1)) / (8 * (1 - Real.exp (-(R + 1)))) ≤ Real.exp (-(R * H)) / 8 := by
  have hq : Real.exp (-(R + 1)) ≤ 1 / 2 := by
    have : Real.exp (-(R + 1)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h1 : Real.exp (-1) < 1 / 2 := by
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg]
      rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    linarith
  have hq0 := Real.exp_pos (-(R + 1))
  have hden : 0 < 8 * (1 - Real.exp (-(R + 1))) := by linarith
  rw [div_le_div_iff₀ hden (by norm_num)]
  have e : Real.exp (-(R + 1) * (H + 1)) = Real.exp (-(R * H)) * Real.exp (-H) * Real.exp (-(R + 1)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e]
  have hH1 : Real.exp (-H) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hRH := Real.exp_pos (-(R * H))
  have hHp := Real.exp_pos (-H)
  nlinarith [mul_le_mul_of_nonneg_left hH1 hRH.le, mul_pos hRH hHp]

end Paper
