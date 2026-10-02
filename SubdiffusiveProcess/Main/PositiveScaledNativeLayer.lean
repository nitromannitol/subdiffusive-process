import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

def positiveScaledNativeLayer {d : ℕ}
    (omega : NativeBilateralPotentialSample d) (n : ℕ) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale
    ((3 : ℝ) ^ (-(n + 1 : ℤ))) (omega (n + 1 : ℕ))

end SubdiffusiveProcess
