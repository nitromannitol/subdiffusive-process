module

public import SubdiffusiveProcess.Assumptions.PotentialField
public import Homogenization.Geometry.CubeMetric

@[expose] public section

/-!
# Unit-cube gradient Lipschitz seminorm
-/

open Homogenization




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm
    {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {p : ({x : Vec d // x ∈ openCubeSet (originCube d 0)} ×
          {x : Vec d // x ∈ openCubeSet (originCube d 0)}) // p.1 ≠ p.2} ↦
    match o with
    | none => 0
    | some p =>
        dist (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g p.1.1.1)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g p.1.2.1) /
          dist p.1.1.1 p.1.2.1)

