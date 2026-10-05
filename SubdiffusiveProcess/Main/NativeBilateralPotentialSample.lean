module

public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

abbrev NativeBilateralPotentialSample (d : ℕ) :=
  ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d

end SubdiffusiveProcess
