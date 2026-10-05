module

public import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

def positiveScaledNativeLayer {d : ℕ}
    (omega : NativeBilateralPotentialSample d) (n : ℕ) :
    _root_.SubdiffusiveProcess.Model.PotentialField d :=
  _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale
    ((3 : ℝ) ^ (-(n + 1 : ℤ))) (omega (n + 1 : ℕ))

end SubdiffusiveProcess
