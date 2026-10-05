module

public import SubdiffusiveProcess.Model.TauSq

@[expose] public section

/-!
# Positive disorder strength

The fourth standing assumption retains exponential integrability and
`tauSq_pos`. The latter already forces the former: the totalized real
integral of a nonintegrable function is zero, and `Real.log 0 = 0`, whereas
`tauSq` is required to be positive. The separate integrability field records
the paper's hypothesis explicitly and is logically redundant. This redundancy
does not further restrict the model class.
-/

open MeasureTheory ProbabilityTheory

/-- Finite exponential moment and positive disorder strength, assumption
(g4). -/
structure SubdiffusiveProcess.Model.ShellLawG4 (d : ℕ)
    (P : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  exponential_integrable :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d ↦ Real.exp (g 0))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure
  tauSq_pos : 0 < _root_.SubdiffusiveProcess.Model.tauSq P
