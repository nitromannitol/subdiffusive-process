module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
public import Homogenization.Geometry.TriadicPartition
public import Homogenization.Geometry.CubeMetric
public import Mathlib.Tactic

@[expose] public section

open Homogenization SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- The rescaled unit cell is contained in the larger ball used to
measure the coarse-field oscillation. -/
theorem lem_as_coarse_shallow_grid_cellMap_mem_osc_ball {d k : ℕ}
    (w y : SpatialCoordinates d)
    (hy : y ∈ openCubeSet (originCube d 0)) :
    aux_lem_as_coarse_shallow_grid_cellMap k w y ∈
      Metric.closedBall w (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)) := by
  have hycoord := (mem_openCubeSet_originCube_iff.mp hy)
  have hyNorm : ‖y‖ ≤ (1 / 2 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro i
    rw [Real.norm_eq_abs]
    have hi := hycoord i
    norm_num at hi
    exact abs_le.mpr ⟨hi.1.le, hi.2.le⟩
  have hp : 0 ≤ (3 : ℝ)^(-(k : ℤ)) := by positivity
  have hmap : aux_lem_as_coarse_shallow_grid_cellMap k w y - w =
      (3 : ℝ)^(-(k : ℤ)) • y := by
    funext i
    simp [aux_lem_as_coarse_shallow_grid_cellMap, cubeDilation_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Metric.mem_closedBall, dist_eq_norm, hmap, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hp]
  nlinarith [mul_le_mul_of_nonneg_left hyNorm hp]

end SubdiffusiveProcess.Paper
