module

public import SubdiffusiveProcess.Assumptions.Observables
public import SubdiffusiveProcess.Model.OGammaLE
public import SubdiffusiveProcess.Model.ZeroPotentialLaw

@[expose] public section

/-!
# Assumption (g2)
-/

open MeasureTheory ProbabilityTheory

/-- Expectation-form stretched-exponential control of the unit-cube
`C¹ˑ¹` observable, assumption (g2), `a.g2`. -/

structure SubdiffusiveProcess.Model.ShellLawG2 (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  regularity_expectation :
    SubdiffusiveProcess.OGammaLE (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure 2 delta
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable

