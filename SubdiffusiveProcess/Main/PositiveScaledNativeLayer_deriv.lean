import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
import SubdiffusiveProcess.Main.PositiveScaledNativeLayer
import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

@[simp] theorem positiveScaledNativeLayer_deriv {d : ℕ}
    (omega : NativeBilateralPotentialSample d) (n : ℕ)
    (x : SpatialCoordinates d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
        (positiveScaledNativeLayer omega n) x =
      ((3 : ℝ) ^ (-(n + 1 : ℤ))) •
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega (n + 1 : ℕ))
          (((3 : ℝ) ^ (-(n + 1 : ℤ))) • x) := rfl

end SubdiffusiveProcess
