module

public import SubdiffusiveProcess.CoarseGrainingVocab.Defect

@[expose] public section

open scoped ENNReal

/-- The normalized response defect `ℳ_m(U)`. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Homogenization.Book.Ch02.Domain d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn U
    (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData M m ω U).toCoeffOn
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)

