module

public import SubdiffusiveProcess.Assumptions.Sample
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-!
# Marginal laws of potential layers
-/

open MeasureTheory ProbabilityTheory

/-- The law of the `k`th potential layer; see the scaling relation in
`a.g1`. -/

noncomputable def SubdiffusiveProcess.Model.potentialMarginalLaw {d : ℕ}
    (P : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
    (k : ℕ) :
    ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
  P.map (fun ω => ω k)

