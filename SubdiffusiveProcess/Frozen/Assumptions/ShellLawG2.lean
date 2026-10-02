import SubdiffusiveProcess.Assumptions.Observables
import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
import SubdiffusiveProcess.Frozen.Assumptions.ZeroPotentialLaw

/-!
# Assumption (g2)
-/

open MeasureTheory ProbabilityTheory




structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  regularity_expectation :
    SubdiffusiveProcess.OGammaLE (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure 2 delta
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable

