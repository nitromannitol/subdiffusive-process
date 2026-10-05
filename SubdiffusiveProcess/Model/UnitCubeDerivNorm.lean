module

public import SubdiffusiveProcess.Assumptions.PotentialField
public import Homogenization.Geometry.CubeMetric

@[expose] public section

/-!
# Unit-cube gradient norm
-/

open Homogenization

/-- The supremum norm of the gradient on the literal open unit cube in
assumption (g2). -/

noncomputable def SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm
    {d : ℕ} (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {x : Vec d // x ∈ openCubeSet (originCube d 0)} ↦
    match o with
    | none => 0
    | some x => ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x.1‖)

