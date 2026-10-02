import SubdiffusiveProcess.Sobolev.FiniteLayerPotentials
import SubdiffusiveProcess.Probability.LayerProductBlocks
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence

open MeasureTheory
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The layer g_j has the law of g_0(3^(-j) ·), in the manuscript index convention. -/
def layerScaling (d : ℕ) (j : ℤ) :
    C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
  ContinuousMap.compRightContinuousMap ℝ
    (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-j) • x,
      continuous_const.smul continuous_id⟩ : C(SpatialCoordinates d, SpatialCoordinates d))

end SubdiffusiveProcess
