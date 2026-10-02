import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
This file proves the final scalar small-cap budget used by the CGE Campanato estimate.
-/

namespace SubdiffusiveProcess

/-- Small parameter caps make the accumulated Campanato loss strictly smaller than `1 - alpha`. -/
theorem campanato_budget_of_small_caps
    (alpha C eps lam delta : ℝ) (hC : 0 < C) (ha : alpha < 1)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1) (hd0 : 0 ≤ delta)
    (he : eps ≤ (1 - alpha) / (4 * C))
    (hl : lam ≤ (1 - alpha) / (4 * C))
    (hd : delta ≤ Real.sqrt ((1 - alpha) / (4 * C))) :
    C * (lam + delta ^ 2 + eps ^ 8) < 1 - alpha := by
  let T : ℝ := (1 - alpha) / (4 * C)
  have hgap : 0 < 1 - alpha := by
    linarith only [ha]
  have hden : 0 < (4 : ℝ) * C := by
    exact mul_pos (by norm_num) hC
  have hT : 0 < T := by
    dsimp [T]
    exact div_pos hgap hden
  have heighth : eps ^ 8 ≤ T := by
    calc
      eps ^ 8 ≤ eps := by
        simpa only [pow_one] using
          (pow_le_pow_of_le_one he0 he1 (by norm_num : 1 ≤ 8))
      _ ≤ T := he
  have hdelta_sq : delta ^ 2 ≤ T := by
    calc
      delta ^ 2 = delta * delta := by
        exact pow_two delta
      _ ≤ Real.sqrt T * Real.sqrt T :=
        mul_le_mul hd hd hd0 (Real.sqrt_nonneg T)
      _ = T := by
        simpa only [pow_two] using Real.sq_sqrt hT.le
  have hparts : lam + delta ^ 2 + eps ^ 8 ≤ T + T + T := by
    exact add_le_add (add_le_add hl hdelta_sq) heighth
  have hsum : lam + delta ^ 2 + eps ^ 8 ≤ 3 * T := by
    calc
      lam + delta ^ 2 + eps ^ 8 ≤ T + T + T := hparts
      _ = 3 * T := by ring
  have hscaled : C * (lam + delta ^ 2 + eps ^ 8) ≤ C * (3 * T) :=
    mul_le_mul_of_nonneg_left hsum hC.le
  have hidentity : C * (3 * T) = 3 * (1 - alpha) / 4 := by
    dsimp [T]
    field_simp [ne_of_gt hC]
  have hquarter : 3 * (1 - alpha) / 4 < 1 - alpha := by
    linarith only [hgap]
  exact lt_of_le_of_lt (hscaled.trans_eq hidentity) hquarter

end SubdiffusiveProcess
