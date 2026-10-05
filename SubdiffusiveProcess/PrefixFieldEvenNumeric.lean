module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SubdiffusiveProcess.Paper

/-- A fixed even moment's root is at most linear in its logarithmic bank
parameter. This crude bound is sufficient for discounted summability. -/
theorem prefix_even_root_le_linear (b : ℝ) (hb : 1 ≤ b)
    (q : ℕ) (hq : 1 ≤ q) :
    (2 * ENNReal.ofReal (b ^ q)) ^ (1 / ((2 * q : ℕ) : ℝ)) ≤
      ENNReal.ofReal (2 * b) := by
  have hb0 : 0 ≤ b := by linarith
  have hpow : b ^ q ≤ b ^ (2 * q) :=
    pow_le_pow_right₀ hb (by omega)
  have htwo : (2 : ℝ) ≤ 2 ^ (2 * q) := by
    have h := pow_le_pow_right₀
      (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ 2 * q by omega)
    simpa using h
  have hscalar : 2 * b ^ q ≤ (2 * b) ^ (2 * q) := by
    rw [mul_pow]
    calc
      2 * b ^ q ≤ 2 * b ^ (2 * q) := by gcongr
      _ ≤ 2 ^ (2 * q) * b ^ (2 * q) := by
        exact mul_le_mul_of_nonneg_right htwo (pow_nonneg hb0 _)
  have hbase : 2 * ENNReal.ofReal (b ^ q) ≤
      ENNReal.ofReal ((2 * b) ^ (2 * q)) := by
    have hcast : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
    rw [hcast]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal hscalar
  calc
    (2 * ENNReal.ofReal (b ^ q)) ^ (1 / ((2 * q : ℕ) : ℝ)) ≤
      ENNReal.ofReal ((2 * b) ^ (2 * q)) ^
        (1 / ((2 * q : ℕ) : ℝ)) :=
      ENNReal.rpow_le_rpow hbase (by positivity)
    _ = ENNReal.ofReal (2 * b) := by
      rw [ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * b), one_div,
        ENNReal.pow_rpow_inv_natCast (show 2 * q ≠ 0 by omega)]


end SubdiffusiveProcess.Paper
