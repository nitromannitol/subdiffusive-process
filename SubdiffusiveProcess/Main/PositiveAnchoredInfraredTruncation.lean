module

public import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer
public import SubdiffusiveProcess.Main.ZeroNativePotentialField
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

def positiveAnchoredInfraredTruncation {d : ℕ}
    (omega : NativeBilateralPotentialSample d) : ℕ →
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField d
  | 0 => zeroNativePotentialField d
  | L + 1 => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
      (positiveAnchoredInfraredTruncation omega L)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor
        (positiveScaledNativeLayer omega L))

end SubdiffusiveProcess
