import SubdiffusiveProcess.Rosenthal.Centered

/-!
# The numerical constants of the Rosenthal inequality

`K_s = (2 e^{-s/2} s^{s/2})^{1/s} = 2^{1/s} e^{-1/2} √s`.  For `p ≥ 2`:
`2 K_p ≤ 6 √p` and `4 K_p K_{p/2} ≤ 4 p`.
-/

namespace SubdiffusiveProcess.Rosenthal

theorem khintchineConst_eq {s : ℝ} (hs : 0 < s) :
    khintchineConst s = 2 ^ (1 / s) * Real.exp (-1 / 2) * Real.sqrt s := by
  unfold khintchineConst
  have h1 : (0 : ℝ) ≤ 2 := by norm_num
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow h1 (Real.exp_pos _).le,
    ← Real.exp_mul, ← Real.rpow_mul hs.le, Real.sqrt_eq_rpow]
  have e1 : -s / 2 * (1 / s) = -1 / 2 := by field_simp
  have e2 : s / 2 * (1 / s) = 1 / 2 := by field_simp
  rw [e1, e2]

theorem khintchineConst_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ khintchineConst s := by
  rw [khintchineConst_eq hs]; positivity

theorem two_rpow_le_sqrt_two {p : ℝ} (hp : 2 ≤ p) : (2 : ℝ) ^ (1 / p) ≤ Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : 0 < p := by linarith
  rw [div_le_div_iff₀ this (by norm_num)]
  linarith

theorem khintchineConst_le {p : ℝ} (hp : 2 ≤ p) :
    khintchineConst p ≤ Real.sqrt 2 * Real.exp (-1 / 2) * Real.sqrt p := by
  have hp0 : 0 < p := by linarith
  rw [khintchineConst_eq hp0]
  gcongr
  exact two_rpow_le_sqrt_two hp

theorem khintchineConst_half_le {p : ℝ} (hp : 2 ≤ p) :
    khintchineConst (p / 2) ≤ Real.sqrt 2 * Real.exp (-1 / 2) * Real.sqrt p := by
  have hp0 : 0 < p := by linarith
  have hr : 1 ≤ p / 2 := by linarith
  rw [khintchineConst_eq (by linarith)]
  have h1 : (2 : ℝ) ^ (1 / (p / 2)) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / (p / 2)) ≤ 2 ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [div_le_one (by linarith)]; exact hr
      _ = 2 := Real.rpow_one 2
  have h2 : Real.sqrt (p / 2) * 2 = Real.sqrt 2 * Real.sqrt p := by
    rw [Real.sqrt_div hp0.le, Real.sqrt_eq_rpow]
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith [this, Real.sqrt_nonneg p, Real.sqrt_nonneg 2]
  calc 2 ^ (1 / (p / 2)) * Real.exp (-1 / 2) * Real.sqrt (p / 2)
      ≤ 2 * Real.exp (-1 / 2) * Real.sqrt (p / 2) := by gcongr
    _ = Real.exp (-1 / 2) * (Real.sqrt (p / 2) * 2) := by ring
    _ = _ := by rw [h2]; ring

theorem constants_le {p : ℝ} (hp : 2 ≤ p) :
    2 * khintchineConst p ≤ 6 * Real.sqrt p ∧
      4 * (khintchineConst p * khintchineConst (p / 2)) ≤ 4 * p := by
  have hp0 : 0 < p := by linarith
  have hK := khintchineConst_le hp
  have hK' := khintchineConst_half_le hp
  have hK0 := khintchineConst_nonneg hp0
  have hKr0 := khintchineConst_nonneg (show 0 < p / 2 by linarith)
  have he : Real.exp (-1 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; norm_num
  have he2 : Real.exp (-1 / 2) * Real.exp (-1 / 2) ≤ 1 / 2 := by
    rw [← Real.exp_add]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have : Real.exp (-1 / 2 + -1 / 2) = (Real.exp 1)⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [this]
    calc (Real.exp 1)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
      _ = 1 / 2 := by norm_num
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs2' : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hsp0 := Real.sqrt_nonneg p
  have hs20 := Real.sqrt_nonneg 2
  have he0 := (Real.exp_pos (-1 / 2)).le
  constructor
  · calc 2 * khintchineConst p ≤ 2 * (Real.sqrt 2 * Real.exp (-1 / 2) * Real.sqrt p) := by gcongr
      _ ≤ 2 * ((3 / 2) * 1 * Real.sqrt p) := by gcongr
      _ ≤ 6 * Real.sqrt p := by nlinarith
  · have : khintchineConst p * khintchineConst (p / 2) ≤
        (Real.sqrt 2 * Real.exp (-1 / 2) * Real.sqrt p) * (Real.sqrt 2 * Real.exp (-1 / 2) * Real.sqrt p) :=
      mul_le_mul hK hK' hKr0 (by positivity)
    have h3 : (Real.sqrt 2 * Real.exp (-1 / 2) * Real.sqrt p) * (Real.sqrt 2 * Real.exp (-1 / 2) * Real.sqrt p)
        = (Real.sqrt 2 * Real.sqrt 2) * (Real.exp (-1 / 2) * Real.exp (-1 / 2)) * (Real.sqrt p * Real.sqrt p) := by
      ring
    rw [h3, hs2', hsp] at this
    nlinarith

end SubdiffusiveProcess.Rosenthal
