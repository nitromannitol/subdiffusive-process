module

public import SubdiffusiveProcess.Model.PotentialMarginalLaw

@[expose] public section

/-!
# The unit-scale potential law
-/

open MeasureTheory ProbabilityTheory

/-- The law of the unit-scale layer `g₀`. -/

noncomputable def SubdiffusiveProcess.Model.zeroPotentialLaw {d : ℕ}
    (P : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d)) :
    ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
  _root_.SubdiffusiveProcess.Model.potentialMarginalLaw P 0

