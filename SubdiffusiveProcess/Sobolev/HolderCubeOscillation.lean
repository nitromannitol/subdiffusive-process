module

public import SubdiffusiveProcess.Sobolev.HolderTraceScaling

@[expose] public section

/-! A global Holder seminorm controls oscillations on the closure of each contained cube.
No extension or form-domain membership is asserted. -/
open Set MeasureTheory TopologicalSpace SubdiffusiveProcess.Lane4
open scoped Topology BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- The closed cube has Euclidean diameter bounded by square-root dimension times side length. -/
theorem euclidean_cube_closure_diameter_le {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    {x y : SpatialCoordinates d}
    (hx : x ∈ closure (Metric.ball z (r / 2)))
    (hy : y ∈ closure (Metric.ball z (r / 2))) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * r := by
  have hx' : dist x z ≤ r / 2 := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hx)
  have hy' : dist y z ≤ r / 2 := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hy)
  have hdist : dist x y ≤ r := by
    have h := dist_triangle x z y
    rw [dist_comm z y] at h
    linarith only [h, hx', hy']
  exact (Paper.aux_lem_goodext_euclid_le x y).trans
    (mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg _))

/-- A global Holder seminorm gives one uniform scaled oscillation bound on all contained cubes. -/
theorem holder_cube_oscillation_le {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {S : Set (SpatialCoordinates d)} {g : SpatialCoordinates d → ℝ} {alpha : ℝ}
    (ha : 0 ≤ alpha) (hsub : closure (Metric.ball z (r / 2)) ⊆ S) (hg : IsHolderOn alpha S g)
    (x y : SpatialCoordinates d) (hx : x ∈ closure (Metric.ball z (r / 2)))
    (hy : y ∈ closure (Metric.ball z (r / 2))) :
    |g y - g x| ≤ ((Real.sqrt d) ^ alpha * holderSeminorm alpha S g) * r ^ alpha := by
  by_cases hxy : y = x
  · rw [hxy, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (holderSeminorm_nonneg _ _ _))
      (Real.rpow_nonneg hr.le _)
  have hp := sqrt_sum_sq_sub_pos hxy
  have hratio : |g y - g x| / (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2)) ^ alpha ≤
      holderSeminorm alpha S g := le_csSup hg ⟨y, hsub hy, x, hsub hx, hxy, rfl⟩
  have hbound := (div_le_iff₀ (Real.rpow_pos_of_pos hp alpha)).mp hratio
  refine hbound.trans ?_
  calc
    holderSeminorm alpha S g * (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2)) ^ alpha ≤
        holderSeminorm alpha S g * (Real.sqrt d * r) ^ alpha :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.sqrt_nonneg _)
        (euclidean_cube_closure_diameter_le z r hy hx) ha) (holderSeminorm_nonneg _ _ _)
    _ = _ := by rw [Real.mul_rpow (Real.sqrt_nonneg _) hr.le]; ring

end SubdiffusiveProcess
