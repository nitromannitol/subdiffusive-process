module

public import SubdiffusiveProcess.Frozen.Assumptions.PotentialMarginalLaw

@[expose] public section

/-!
# The unit-scale potential law
-/

open MeasureTheory ProbabilityTheory




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) :
    ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
  SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw P 0

