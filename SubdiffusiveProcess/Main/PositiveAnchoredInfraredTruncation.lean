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
      _root_.SubdiffusiveProcess.Model.PotentialField d
  | 0 => zeroNativePotentialField d
  | L + 1 => _root_.SubdiffusiveProcess.Model.PotentialField.add
      (positiveAnchoredInfraredTruncation omega L)
      (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
        (positiveScaledNativeLayer omega L))

end SubdiffusiveProcess
