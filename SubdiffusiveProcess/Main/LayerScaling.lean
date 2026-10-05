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

/-- The layer g_j has the law of g_0(3^(-j) ·), in the manuscript index convention. -/
def layerScaling (d : ℕ) (j : ℤ) :
    C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
  ContinuousMap.compRightContinuousMap ℝ
    (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-j) • x,
      continuous_const_smul ((3 : ℝ) ^ (-j))⟩ : C(SpatialCoordinates d, SpatialCoordinates d))

end SubdiffusiveProcess
