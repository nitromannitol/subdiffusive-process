module

public import SubdiffusiveProcess.Frozen.Assumptions.TauSq

@[expose] public section

/-!
# Assumption (g4)
-/

open MeasureTheory ProbabilityTheory




structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG4 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  exponential_integrable :
    Integrable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d ↦ Real.exp (g 0))
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure
  tauSq_pos : 0 < SubdiffusiveProcess.Frozen.Assumptions.tauSq P

