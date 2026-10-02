import SubdiffusiveProcess.Assumptions.Sample
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Marginal laws of potential layers
-/

open MeasureTheory ProbabilityTheory




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (k : ℕ) :
    ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
  P.map (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k).aemeasurable

