module

public import SubdiffusiveProcess.Frozen.Assumptions.ZeroPotentialLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Disorder strength
-/

open MeasureTheory ProbabilityTheory




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.tauSq {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : ℝ :=
  Real.log
    (∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g 0)
      ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure)

