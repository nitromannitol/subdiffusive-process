import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Convert a Euclidean coordinate Hölder estimate to the ambient supremum metric.
Only the deterministic dimension factor changes. -/
open Homogenization
open scoped BigOperators
namespace SubdiffusiveProcess

/-- A coordinate Euclidean Hölder bound implies a bound for the ambient metric. -/
theorem euclidean_holder_le_metric {d : ℕ} (x y : Fin d → ℝ)
    {alpha C v : ℝ} (ha : 0 ≤ alpha) (hC : 0 ≤ C)
    (h : v ≤ C * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha) :
    v ≤ (C * (d : ℝ) ^ alpha) * dist x y ^ alpha := by
  have he : Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤ (d : ℝ) * dist x y := by
    simpa only [euclideanNorm, vecNormSq, vecDot, Pi.sub_apply, ← pow_two, dist_eq_norm]
      using euclideanNorm_le_dimension_mul_norm (x - y)
  calc
    v ≤ C * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha := h
    _ ≤ C * ((d : ℝ) * dist x y) ^ alpha :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.sqrt_nonneg _) he ha) hC
    _ = (C * (d : ℝ) ^ alpha) * dist x y ^ alpha := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) dist_nonneg, mul_assoc]

end SubdiffusiveProcess
