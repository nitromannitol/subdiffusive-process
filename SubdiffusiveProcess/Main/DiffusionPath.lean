module

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

/-- Continuous trajectories with the compact-open topology on nonnegative time. -/
abbrev DiffusionPath (d : ℕ) := C(ℝ≥0, SpatialCoordinates d)

end SubdiffusiveProcess
