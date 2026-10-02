import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace SubdiffusiveProcess.Nash

/-- Algebra of the coefficient in the Nash differential inequality. -/
theorem decay_constant (d : ℕ) (hd : 0 < d) (K F t : ℝ) (hK : 0 < K) (hF : 0 < F)
    (ht : 0 < t) :
    (2 / ((d : ℝ) * K * F ^ (2 / (d : ℝ))) * t) ^ (-(d : ℝ)) =
      ((d : ℝ) * K / (2 * t)) ^ d * F ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : 0 < F ^ (2 / (d : ℝ)) := Real.rpow_pos_of_pos hF _
  have hbase : 2 / ((d : ℝ) * K * F ^ (2 / (d : ℝ))) * t =
      (((d : ℝ) * K / (2 * t)) * F ^ (2 / (d : ℝ)))⁻¹ := by
    field_simp
  rw [hbase, ← Real.rpow_neg_eq_inv_rpow, neg_neg, Real.rpow_natCast, mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hF.le]
  have : (2 / (d : ℝ)) * d = 2 := by field_simp
  rw [this, Real.rpow_two]

end SubdiffusiveProcess.Nash
