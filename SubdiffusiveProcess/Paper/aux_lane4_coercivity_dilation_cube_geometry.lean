module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.CubeDilation
public import Homogenization.Sobolev.H1.Translation

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Statement-only fine child: the translated and scaled cube identities used at paper lines 395--396. -/
theorem aux_lane4_coercivity_dilation_cube_geometry (d : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) =
        Homogenization.translateSet z
          (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) ∧
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
        r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
  constructor
  · change Metric.ball z (r / 2) =
      Homogenization.translateSet z (Metric.ball (0 : SpatialCoordinates d) (r / 2))
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    simp only [Metric.mem_ball]
    rw [dist_eq_norm, dist_eq_norm]
    simp
  · change Metric.ball (0 : SpatialCoordinates d) (r / 2) =
      r • Metric.ball (0 : SpatialCoordinates d) (1 / 2)
    rw [_root_.smul_ball hr.ne']
    simp [abs_of_pos hr]
    ring_nf


end Paper
