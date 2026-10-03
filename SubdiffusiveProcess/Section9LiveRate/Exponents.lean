module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

namespace SubdiffusiveProcess.Section9LiveRate

/-- The masking rate is stronger than the fine-layer influence rate. -/
theorem masking_decay_le_influence_decay (b : ℝ) (hb : 0 ≤ b) (j : ℕ) :
    (3 : ℝ) ^ (-(3 * b / 8) * (j : ℝ)) ≤
      (3 : ℝ) ^ (-(b / 8) * (j : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith [mul_nonneg hb hj]

/-- The paper's exponent `b/8` is positive and at most one. -/
theorem influence_exponent_pos_le_one (d : ℕ) (hd : 2 ≤ d) (t : ℝ)
    (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ)) :
    0 < t * (t - (d : ℝ) + 1) / (t + 1) / 8 ∧
      t * (t - (d : ℝ) + 1) / (t + 1) / 8 ≤ 1 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 < t := by linarith
  have h1 : 0 < t - d + 1 := by linarith
  have h2 : t - d + 1 < 1 := by linarith
  constructor
  · positivity
  · have hb : t * (t - d + 1) / (t + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      nlinarith
    linarith

end SubdiffusiveProcess.Section9LiveRate
