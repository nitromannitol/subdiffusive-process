import SubdiffusiveProcess.Frozen.Assumptions.UnitCubeValueNorm
import SubdiffusiveProcess.Frozen.Assumptions.UnitCubeDerivNorm
import SubdiffusiveProcess.Frozen.Assumptions.UnitCubeDerivLipschitzSeminorm

/-!
# The regularity observable in assumption (g2)
-/




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable {d : ℕ}
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm g +
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm g +
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm g

