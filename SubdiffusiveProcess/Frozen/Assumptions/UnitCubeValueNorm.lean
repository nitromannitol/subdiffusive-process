import SubdiffusiveProcess.Assumptions.PotentialField
import Homogenization.Geometry.CubeMetric

/-!
# Unit-cube value norm
-/

open Homogenization




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm
    {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {x : Vec d // x ∈ openCubeSet (originCube d 0)} ↦
    match o with
    | none => 0
    | some x => |g x.1|)

