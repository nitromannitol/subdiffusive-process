import SubdiffusiveProcess.Main.LayerScaling
import SubdiffusiveProcess.Sobolev.FiniteLayerPotentials
import SubdiffusiveProcess.Probability.LayerProductBlocks
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence

open MeasureTheory
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The literal scaled coordinate law on continuous fields. -/
def scaledLayerLaw (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) (j : ℤ) :
    ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
  ν.map (layerScaling d j).continuous.measurable.aemeasurable

end SubdiffusiveProcess
