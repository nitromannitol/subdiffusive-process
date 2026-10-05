module

public import SubdiffusiveProcess.Geometry.Cube
public import Homogenization.Geometry.CubeMetric
public import Homogenization.Multiscale.NormalizedNorms

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The physical cube used by the section is the open realization of the
same triadic cube in the imported deterministic estimates. -/
theorem centeredCube_eq_openCubeSet {d : ℕ}
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q) :
    (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet Q := by
  change Metric.ball _ _ = _
  simpa only [Homogenization.cubeRadius, one_div, div_eq_mul_inv, mul_comm, one_mul] using
    Homogenization.ball_cubeCenter_eq_openCubeSet Q

/-- The open-domain L2 measure agrees with the half-open cube measure used
by the imported coarse-graining norms; boundaries have zero volume. -/
theorem centeredCube_restrict_volume_eq_cubeMeasure {d : ℕ}
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q) :
    volume.restrict (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d)) =
      Homogenization.cubeMeasure Q := by
  rw [centeredCube_eq_openCubeSet]
  exact (Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q).symm

end SubdiffusiveProcess
