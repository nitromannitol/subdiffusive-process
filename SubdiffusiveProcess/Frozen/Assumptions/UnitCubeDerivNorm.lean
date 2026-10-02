import SubdiffusiveProcess.Assumptions.PotentialField
import Homogenization.Geometry.CubeMetric

/-!
# Unit-cube gradient norm
-/

open Homogenization




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm
    {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {x : Vec d // x ∈ openCubeSet (originCube d 0)} ↦
    match o with
    | none => 0
    | some x => ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x.1‖)

