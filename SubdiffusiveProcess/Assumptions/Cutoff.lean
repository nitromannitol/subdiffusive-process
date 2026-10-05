module

public import SubdiffusiveProcess.Model.ACutoff
public import SubdiffusiveProcess.Assumptions.Sample

@[expose] public section

/-!
# Basic properties of the finite cutoff
-/



namespace SubdiffusiveProcess.Model

open Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ}

theorem aCutoff_pos (M : GMCModel d) (L : ℕ)
    (ω : PotentialSample d) (x : Vec d) :
    0 < aCutoff M L ω x :=
  Real.exp_pos _

theorem measurable_aCutoff (M : GMCModel d) (L : ℕ) (x : Vec d) :
    Measurable (fun ω : PotentialSample d ↦ aCutoff M L ω x) := by
  apply Measurable.exp
  apply Finset.measurable_sum
  intro k _hk
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
      (measurable_potentialCoordinate k) |>.sub measurable_const

theorem continuous_aCutoff (M : GMCModel d) (L : ℕ)
    (ω : PotentialSample d) : Continuous (aCutoff M L ω) := by
  apply Real.continuous_exp.comp
  apply continuous_finsetSum
  intro k _hk
  exact (ω k).1.1.continuous.sub continuous_const

end

end SubdiffusiveProcess.Model
