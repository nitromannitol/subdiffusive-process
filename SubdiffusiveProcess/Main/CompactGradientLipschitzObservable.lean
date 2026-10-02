import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

def compactGradientLipschitzObservable {d : ℕ}
    (K : Compacts (SpatialCoordinates d))
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup {a : ℝ | ∃ x y : K, x ≠ y ∧
    a = ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x.1 -
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g y.1‖ / ‖x.1 - y.1‖}

end SubdiffusiveProcess
