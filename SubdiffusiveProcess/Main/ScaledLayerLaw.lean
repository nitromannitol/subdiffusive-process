module

public import SubdiffusiveProcess.Main.LayerScaling
public import SubdiffusiveProcess.Sobolev.FiniteLayerPotentials
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.UniformSpace.CompactConvergence

@[expose] public section

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
  ν.map (layerScaling d j)

end SubdiffusiveProcess
