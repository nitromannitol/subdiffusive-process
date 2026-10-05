module

public import SubdiffusiveProcess.Sobolev.FiniteLayerPotentials
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.UniformSpace.CompactConvergence

@[expose] public section

/-!
# Continuous diffusion paths

`DiffusionPath d` is the space of continuous maps from nonnegative time
`ℝ≥0` to `SpatialCoordinates d`, with the compact-open topology. Markov
kernels in Theorem A take probability laws on this path space. These paths
have no cemetery state; killed or finite-lifetime processes use the distinct
`MarkovProcess.LifetimePath` carrier.
-/

open MeasureTheory
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- Continuous trajectories with the compact-open topology on nonnegative time. -/
abbrev DiffusionPath (d : ℕ) := C(ℝ≥0, SpatialCoordinates d)

end SubdiffusiveProcess
