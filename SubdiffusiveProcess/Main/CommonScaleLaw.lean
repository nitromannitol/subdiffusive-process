module

public import SubdiffusiveProcess.Main.ScaledLayerLaw
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

/-- The probability law of one bilateral field in the common scale coupling. -/
def commonScaleLaw (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
    ProbabilityMeasure (ℤ → C(SpatialCoordinates d, ℝ)) :=
  ⟨Measure.infinitePi (fun j : ℤ => (scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))),
    inferInstance⟩

end SubdiffusiveProcess
