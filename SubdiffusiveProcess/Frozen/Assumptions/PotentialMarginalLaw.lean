module

public import SubdiffusiveProcess.Assumptions.Sample
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-!
# Marginal laws of potential layers
-/

open MeasureTheory ProbabilityTheory




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (k : ℕ) :
    ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
  P.map (fun ω => ω k)

