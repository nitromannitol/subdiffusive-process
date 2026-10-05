module

public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

def compactGradientLipschitzObservable {d : ℕ}
    (K : Compacts (SpatialCoordinates d))
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  sSup {a : ℝ | ∃ x y : K, x ≠ y ∧
    a = ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x.1 -
          _root_.SubdiffusiveProcess.Model.PotentialField.deriv g y.1‖ / ‖x.1 - y.1‖}

end SubdiffusiveProcess
