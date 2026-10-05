module

public import SubdiffusiveProcess.Assumptions.PotentialField
public import Homogenization.Geometry.CubeMetric

@[expose] public section

/-!
# Unit-cube gradient Lipschitz seminorm
-/

open Homogenization

/-- The Lipschitz seminorm of the gradient on the literal open unit cube,
the `C¹ˑ¹` third term in assumption (g2), `a.g2`.  The `none` index supplies zero when there are no distinct pairs. -/
noncomputable def SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm
    {d : ℕ} (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {p : ({x : Vec d // x ∈ openCubeSet (originCube d 0)} ×
          {x : Vec d // x ∈ openCubeSet (originCube d 0)}) // p.1 ≠ p.2} ↦
    match o with
    | none => 0
    | some p =>
        dist (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g p.1.1.1)
            (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g p.1.2.1) /
          dist p.1.1.1 p.1.2.1)
