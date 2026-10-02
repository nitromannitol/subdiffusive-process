import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
import SubdiffusiveProcess.Main.PositiveScaledNativeLayer
import SubdiffusiveProcess.Main.ZeroNativePotentialField
import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

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
