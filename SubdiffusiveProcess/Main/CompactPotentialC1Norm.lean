import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

def compactPotentialC1Norm {d : ℕ}
    (K : Compacts (SpatialCoordinates d))
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  ‖(⟨fun x : K => g x.1, g.1.1.continuous.comp continuous_subtype_val⟩ : C(K, ℝ))‖ +
    ‖(⟨fun x : K => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x.1,
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g).continuous.comp
          continuous_subtype_val⟩ : C(K, SpatialCoordinates d →L[ℝ] ℝ))‖

end SubdiffusiveProcess
