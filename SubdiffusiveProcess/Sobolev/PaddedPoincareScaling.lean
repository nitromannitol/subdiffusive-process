module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! The dimensional coefficient in the padded-cube Poincare bound is written as a squared scale. -/
noncomputable section
namespace SubdiffusiveProcess

/-- The padded-cube prefactor separates its deterministic, layer, and radius factors. -/
theorem padded_poincare_prefactor
    (d : ℕ) (C g cell r t : ℝ) (hg : 0 < g) (hcell : 0 < cell) (hr : 0 < r) :
    C ^ 2 * (3 * r) ^ 2 * (g * (cell / (2 * Real.exp t)))⁻¹ / (3 * r) ^ d =
      (Real.sqrt (C ^ 2 * 18 / (g * cell * (3 : ℝ) ^ d)) * Real.exp (t / 2)) ^ 2 *
        r ^ (2 - (d : ℝ)) := by
  have hp : r ^ (2 - (d : ℝ)) = r ^ 2 / r ^ d := by
    rw [Real.rpow_sub hr, Real.rpow_two, Real.rpow_natCast]
  have hExp : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [mul_pow]
  rw [Real.sq_sqrt (by positivity), hExp, hp]
  field_simp
  ring

end SubdiffusiveProcess
