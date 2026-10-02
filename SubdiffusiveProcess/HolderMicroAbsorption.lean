import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- A positive power-law gain absorbs a smaller exponential-in-cutoff loss. -/
theorem aux_holder_micro_absorb (a b : ℝ) (ha : 0 < a)
    (hb : b ≤ a * Real.log 3) (N : ℕ) :
    Real.exp (b * (N : ℝ)) * (3 : ℝ) ^ (-a * (N : ℝ)) ≤ 1 := by
  have h3pos : 0 < (3 : ℝ) := by norm_num
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  rw [Real.rpow_def_of_pos h3pos (-a * (N : ℝ))]
  rw [← Real.exp_add]
  rw [Real.exp_le_one_iff]
  have hsum : b * (N : ℝ) + Real.log 3 * (-a * (N : ℝ)) ≤ 0 := by
    have : b * (N : ℝ) + Real.log 3 * (-a * (N : ℝ)) =
        (b - a * Real.log 3) * (N : ℝ) := by ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hNnonneg
  exact hsum


end Paper
