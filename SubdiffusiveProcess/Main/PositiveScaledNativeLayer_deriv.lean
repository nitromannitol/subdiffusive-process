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

@[simp] theorem positiveScaledNativeLayer_deriv {d : ℕ}
    (omega : NativeBilateralPotentialSample d) (n : ℕ)
    (x : SpatialCoordinates d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.deriv
        (positiveScaledNativeLayer omega n) x =
      ((3 : ℝ) ^ (-(n + 1 : ℤ))) •
        _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega (n + 1 : ℕ))
          (((3 : ℝ) ^ (-(n + 1 : ℤ))) • x) := rfl

end SubdiffusiveProcess
