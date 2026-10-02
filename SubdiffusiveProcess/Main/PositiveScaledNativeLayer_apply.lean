import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
import SubdiffusiveProcess.Main.PositiveScaledNativeLayer
import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

@[simp] theorem positiveScaledNativeLayer_apply {d : ℕ}
    (omega : NativeBilateralPotentialSample d) (n : ℕ)
    (x : SpatialCoordinates d) :
    positiveScaledNativeLayer omega n x =
      omega (n + 1 : ℕ) (((3 : ℝ) ^ (-(n + 1 : ℤ))) • x) := rfl

end SubdiffusiveProcess
