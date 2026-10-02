import SubdiffusiveProcess.Sobolev.FiniteLayerPotentials
import SubdiffusiveProcess.Probability.LayerProductBlocks
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence

open MeasureTheory
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- Continuous trajectories with the compact-open topology on nonnegative time. -/
abbrev DiffusionPath (d : ℕ) := C(ℝ≥0, SpatialCoordinates d)

end SubdiffusiveProcess
