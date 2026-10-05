module

public import Mathlib.Basic.ENNReal.Inv

@[expose] public section

open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Nash

theorem dimension_constant (d : ℕ) (K : ℝ) (hK : 0 ≤ K) (t : ℝ≥0) (ht : 0 < t) :
    ENNReal.ofReal (((d : ℝ) * K / (t : ℝ)) ^ d) =
      ENNReal.ofReal ((d : ℝ) ^ d) * (ENNReal.ofReal K / (t : ℝ≥0∞)) ^ d := by
  have htR : (0 : ℝ) < t := ht
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg d),
    ENNReal.ofReal_div_of_pos htR, ENNReal.ofReal_mul (Nat.cast_nonneg d)]
  rw [← mul_pow]
  congr 1
  rw [mul_div_assoc]
  congr 1
  rw [ENNReal.ofReal_coe_nnreal]

end SubdiffusiveProcess.Nash
