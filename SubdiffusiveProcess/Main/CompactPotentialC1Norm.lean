module

public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

def compactPotentialC1Norm {d : ℕ}
    (K : Compacts (SpatialCoordinates d))
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  ‖(⟨fun x : K => g x.1, g.1.1.continuous.comp continuous_subtype_val⟩ : C(K, ℝ))‖ +
    ‖(⟨fun x : K => _root_.SubdiffusiveProcess.Model.PotentialField.deriv g x.1,
        (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.comp
          continuous_subtype_val⟩ : C(K, SpatialCoordinates d →L[ℝ] ℝ))‖

end SubdiffusiveProcess
