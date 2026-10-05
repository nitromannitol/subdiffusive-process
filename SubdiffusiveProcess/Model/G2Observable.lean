module

public import SubdiffusiveProcess.Model.UnitCubeValueNorm
public import SubdiffusiveProcess.Model.UnitCubeDerivNorm
public import SubdiffusiveProcess.Model.UnitCubeDerivLipschitzSeminorm

@[expose] public section

/-!
# The regularity observable in assumption (g2)
-/

/-- Value supremum plus gradient supremum plus gradient Lipschitz seminorm on
the open unit cube, as in (g2), `a.g2`. -/

noncomputable def SubdiffusiveProcess.Model.PotentialField.g2Observable {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm g +
    _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm g +
      _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm g

