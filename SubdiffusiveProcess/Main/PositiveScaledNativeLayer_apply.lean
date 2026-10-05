module

public import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

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
