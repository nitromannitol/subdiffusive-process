module

public import SubdiffusiveProcess.Frozen.Assumptions.UnitCubeValueNorm
public import SubdiffusiveProcess.Frozen.Assumptions.UnitCubeDerivNorm
public import SubdiffusiveProcess.Frozen.Assumptions.UnitCubeDerivLipschitzSeminorm

@[expose] public section

/-!
# The regularity observable in assumption (g2)
-/




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable {d : ℕ}
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm g +
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm g +
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm g

