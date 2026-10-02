import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

abbrev NativeBilateralPotentialSample (d : ℕ) :=
  ℤ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d

end SubdiffusiveProcess
