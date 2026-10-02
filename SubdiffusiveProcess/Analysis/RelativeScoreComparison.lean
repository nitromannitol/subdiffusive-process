import SubdiffusiveProcess.Lane3.Elementary

/-! Relative errors pass to bounded ramps and clipped square roots.
These are deterministic scalar estimates; they assert no probabilistic
comparison of response coordinates or primitive scores.
-/
namespace SubdiffusiveProcess
open Lane3

/-- A small relative error based at the left endpoint also gives a right-based upper bound. -/
theorem relative_le_of_abs_le_left {x y eta : ℝ}
    (hy : 0 ≤ y) (heta : 0 ≤ eta) (heta2 : eta ≤ 1 / 2)
    (hxy : |x - y| ≤ eta * (1 + x)) :
    x ≤ (1 + 2 * eta) * y + 2 * eta := by
  have hleft := (le_abs_self (x - y)).trans hxy
  have hpos : 0 < 1 - eta := by linarith only [heta2]
  have hslack : 0 ≤ eta * (1 - 2 * eta) * (1 + y) :=
    mul_nonneg (mul_nonneg heta (by linarith only [heta2])) (by linarith only [hy])
  have hmul : (1 - eta) * x ≤ (1 - eta) * ((1 + 2 * eta) * y + 2 * eta) := by
    nlinarith only [hleft, hslack]
  exact le_of_mul_le_mul_left hmul hpos

/-- A nonnegative discount at most one preserves a one-sided relative error. -/
theorem discounted_relative_le {w x y eta : ℝ}
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (heta : 0 ≤ eta)
    (hxy : x ≤ (1 + eta) * y + eta) :
    w * x ≤ (1 + eta) * (w * y) + eta := by
  have hmul := mul_le_mul_of_nonneg_left hxy hw
  have herr := mul_le_mul_of_nonneg_right hw1 heta
  nlinarith only [hmul, herr]

/-- The standard bounded ramp is monotone in its argument. -/
theorem ramp_mono_argument {a b x y : ℝ} (hab : a < b) (hxy : x ≤ y) :
    ramp a b x ≤ ramp a b y := by
  exact min_le_min_left 1 (max_le_max_left 0
    (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le))

/-- A bounded ramp turns a one-sided relative error into an absolute error. -/
theorem ramp_le_of_relative_le {a b x y eta : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (heta : 0 ≤ eta)
    (hxy : x ≤ (1 + eta) * y + eta) :
    ramp a b x ≤ ramp a b y + eta * (1 + b) / (b - a) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hb : 0 < b := ha.trans_lt hab
  have herr : 0 ≤ eta * (1 + b) / (b - a) :=
    div_nonneg (mul_nonneg heta (by linarith only [hb])) hba.le
  by_cases hy : b ≤ y
  · rw [ramp_eq_one_of_le hab hy]
    exact (ramp_le_one a b x).trans (le_add_of_nonneg_right herr)
  · have hyb : y ≤ b := (lt_of_not_ge hy).le
    by_cases horder : x ≤ y
    · exact (ramp_mono_argument hab horder).trans (le_add_of_nonneg_right herr)
    · have hdiff : x - y ≤ eta * (1 + b) := by
        have he := mul_le_mul_of_nonneg_left hyb heta
        nlinarith only [hxy, he]
      have hlip := abs_ramp_sub_ramp_le (x := x) (y := y) hab
      rw [abs_of_nonneg (sub_nonneg.mpr (lt_of_not_ge horder).le)] at hlip
      have hbound := (le_abs_self (ramp a b x - ramp a b y)).trans
        (hlip.trans (div_le_div_of_nonneg_right hdiff hba.le))
      linarith only [hbound]

/-- Clipping at one turns a one-sided relative error into an error of twice its size. -/
theorem min_one_le_of_relative_le {x y eta : ℝ} (heta : 0 ≤ eta)
    (hxy : x ≤ (1 + eta) * y + eta) :
    min x 1 ≤ min y 1 + 2 * eta := by
  by_cases hy : 1 ≤ y
  · rw [min_eq_right hy]
    exact (min_le_right x 1).trans (by linarith only [heta])
  · rw [min_eq_left (lt_of_not_ge hy).le]
    have he := mul_le_mul_of_nonneg_left (lt_of_not_ge hy).le heta
    have hm := min_le_left x 1
    nlinarith only [hxy, he, hm]

/-- The clipped square root turns a relative error into a square-root error. -/
theorem sqrt_min_one_le_of_relative_le {x y eta : ℝ}
    (hy : 0 ≤ y) (heta : 0 ≤ eta) (hxy : x ≤ (1 + eta) * y + eta) :
    Real.sqrt (min x 1) ≤ Real.sqrt (min y 1) + Real.sqrt (2 * eta) := by
  apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
  have hs := Real.sq_sqrt (le_min hy zero_le_one)
  have he := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) heta)
  have hp := mul_nonneg (Real.sqrt_nonneg (min y 1)) (Real.sqrt_nonneg (2 * eta))
  have hle := min_one_le_of_relative_le heta hxy
  nlinarith only [hs, he, hp, hle]

end SubdiffusiveProcess
