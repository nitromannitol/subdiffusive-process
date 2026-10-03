module

public import SubdiffusiveProcess.Analysis.GeometricConvolution
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Sqrt

@[expose] public section

/-! # The exact geometric constants for triadic coarse errors

The strict range `0 < s < 1/2` gives both geometric gaps. Algebra below
keeps the constants in the original displayed R2 normalization.
-/
noncomputable section
namespace SubdiffusiveProcess

/-- The square-root third is the triadic half-exponent discount. -/
theorem sqrt_third_eq_triadic_rpow :
    Real.sqrt (1/3 : ℝ) = (3 : ℝ)^(-(1/2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg_one,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- The square-root convolution ratio is strictly smaller than the coarse discount. -/
theorem triadic_sqrt_discount_gap {s : ℝ} (hs : s < 1/2) :
    Real.sqrt (1/3 : ℝ) < (3 : ℝ)^(-s) := by
  rw [sqrt_third_eq_triadic_rpow]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)

/-- The defect convolution ratio is strictly smaller than the squared coarse discount. -/
theorem triadic_square_discount_gap {s : ℝ} (hs : s < 1/2) :
    (1/3 : ℝ) < (3 : ℝ)^(-(2*s)) := by
  have h : (3 : ℝ)^(-1 : ℝ) < (3 : ℝ)^(-(2*s)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  simpa only [Real.rpow_neg_one, one_div] using h

/-- The direct convolution constant equals the displayed squared-error R2 constant. -/
theorem triadic_square_discount_constant (C : ℝ) {s : ℝ} (hs : s < 1/2) :
    1 + C / ((3 : ℝ)^(-(2*s)) - 1/3) =
      1 + 3*C / ((3 : ℝ)^(1-2*s) - 1) := by
  have he : (3 : ℝ)^(1-2*s) = (3 : ℝ)^(-(2*s)) * 3 := by
    have h := Real.rpow_add (by norm_num : (0 : ℝ) < 3) (-(2*s)) 1
    rw [Real.rpow_one] at h
    convert h using 1
    congr 1
    ring
  rw [he]
  have hg : 0 < (3 : ℝ)^(-(2*s)) - 1/3 := sub_pos.mpr (triadic_square_discount_gap hs)
  have hg' : 0 < (3 : ℝ)^(-(2*s)) * 3 - 1 := by linarith
  field_simp

/-- The square-root convolution constant equals the displayed first-error R2 constant. -/
theorem triadic_sqrt_discount_constant (C : ℝ) {s : ℝ} (hs : s < 1/2) :
    1 + Real.sqrt C / ((3 : ℝ)^(-s) - Real.sqrt (1/3 : ℝ)) =
      1 + Real.sqrt (3*C) / ((3 : ℝ)^(1/2-s) - 1) := by
  have hroot : Real.sqrt (1/3 : ℝ) * Real.sqrt 3 = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
    norm_num
  have he : (3 : ℝ)^(1/2-s) = (3 : ℝ)^(-s) * Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hg : 0 < (3 : ℝ)^(-s) - Real.sqrt (1/3 : ℝ) := sub_pos.mpr (triadic_sqrt_discount_gap hs)
  have hg' : 0 < (3 : ℝ)^(1/2-s) - 1 := by
    exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by linarith))
  rw [he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [he] at hg'
  field_simp
  have hm := congrArg (fun x : ℝ => Real.sqrt C * x) hroot
  nlinarith only [hm]

end SubdiffusiveProcess
