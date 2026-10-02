import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Scalar arithmetic for the coarse Poincare energy conversion.
These lemmas square a normalized energy estimate and separate its reference
coefficient; they assert no differential equation or regularity estimate.
-/

namespace SubdiffusiveProcess

/-- The square of a negative half power of a positive scalar is its reciprocal. -/
theorem rpow_neg_half_sq {a : ℝ} (ha : 0 < a) :
    (a ^ (-(1 / 2) : ℝ)) ^ 2 = a⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  norm_num [Real.rpow_neg_one]

/-- Squaring a nonnegative coarse Poincare estimate separates the reference coefficient. -/
theorem sq_le_coarse_energy_of_le_sqrt
    {osc C r rho s energy vol : ℝ}
    (hosc : 0 ≤ osc) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hrho : 0 < rho) (hs : 0 < s) (henergy : 0 ≤ energy) (hvol : 0 < vol)
    (h : osc ≤ C * r * (rho * s) ^ (-(1 / 2) : ℝ) * Real.sqrt (energy / vol)) :
    osc ^ 2 ≤ (C ^ 2 * r ^ 2 * rho⁻¹ / vol) * s⁻¹ * energy := by
  have hright : 0 ≤ C * r * (rho * s) ^ (-(1 / 2) : ℝ) * Real.sqrt (energy / vol) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hr) (Real.rpow_nonneg (mul_pos hrho hs).le _))
      (Real.sqrt_nonneg _)
  have hh : osc ^ 2 ≤
      (C * r * (rho * s) ^ (-(1 / 2) : ℝ) * Real.sqrt (energy / vol)) ^ 2 :=
    (sq_le_sq₀ hosc hright).mpr h
  calc
    osc ^ 2 ≤ (C * r * (rho * s) ^ (-(1 / 2) : ℝ) * Real.sqrt (energy / vol)) ^ 2 := hh
    _ = (C ^ 2 * r ^ 2 * rho⁻¹ / vol) * s⁻¹ * energy := by
      rw [mul_pow, mul_pow, mul_pow, rpow_neg_half_sq (mul_pos hrho hs),
        Real.sq_sqrt (div_nonneg henergy hvol.le), mul_inv_rev]
      ring

end SubdiffusiveProcess
