module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The triadic series of the growth bound

The growth bound of `mfd:prop-chaos-growth` (paper label `mfd:prop-chaos-growth`) sums, over the
triadic layers `j`, a term whose size is `3 ^ (-j theta)` with
`theta = p epsilon - d - Cexponent delta ^ 2`.  The whole point of the choice
of `p` from `epsilon` and then of `delta` from both is that `theta > 0`, at
which point the series is geometric.  This file is that step, isolated from
the probability.
-/

open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- `3 ^ (-(j theta))` is the `j`-th power of `3 ^ (-theta)`. -/
theorem three_rpow_neg_mul (theta : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (-(j : ℝ) * theta) = ((3 : ℝ) ^ (-theta)) ^ j := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-theta)) j, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- The triadic series converges as soon as the exponent is positive. -/
theorem tsum_ofReal_three_rpow_lt_top {theta : ℝ} (htheta : 0 < theta) {C : ℝ}
    (hC : 0 ≤ C) :
    ∑' j : ℕ, ENNReal.ofReal (C * (3 : ℝ) ^ (-(j : ℝ) * theta)) < ⊤ := by
  have hx0 : (0 : ℝ) < (3 : ℝ) ^ (-theta) := Real.rpow_pos_of_pos (by norm_num) _
  have hx1 : (3 : ℝ) ^ (-theta) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set x : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ (-theta)) with hxdef
  have hxlt : x < 1 := by
    rw [hxdef, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr hx1
  have hterm : ∀ j : ℕ, ENNReal.ofReal (C * (3 : ℝ) ^ (-(j : ℝ) * theta))
      = ENNReal.ofReal C * x ^ j := by
    intro j
    rw [three_rpow_neg_mul theta j, ENNReal.ofReal_mul hC, hxdef,
      ← ENNReal.ofReal_pow hx0.le]
  calc ∑' j : ℕ, ENNReal.ofReal (C * (3 : ℝ) ^ (-(j : ℝ) * theta))
      = ∑' j : ℕ, ENNReal.ofReal C * x ^ j := by simp_rw [hterm]
    _ = ENNReal.ofReal C * ∑' j : ℕ, x ^ j := by rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal C * (1 - x)⁻¹ := by rw [ENNReal.tsum_geometric]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [ENNReal.inv_lt_top]
        exact tsub_pos_of_lt hxlt

end SubdiffusiveProcess
