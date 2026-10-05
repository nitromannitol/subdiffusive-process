module

public import SubdiffusiveProcess.CoarseGrainingVocab.Core

@[expose] public section

open scoped ENNReal

/-- The paper's one-cube normalized response maximum. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax {d : ℕ}
    (Q : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d)
    (a : Homogenization.Book.Ch02.TriadicCoeffFamily d) (alpha : ℝ) : ℝ≥0∞ :=
  ⨆ e : {e : SubdiffusiveProcess.CoarseGrainingVocab.Vec d //
      Homogenization.vecNormSq e = 1},
    ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe Q a alpha e)

