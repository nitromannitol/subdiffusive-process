import SubdiffusiveProcess.CoarseGrainingVocab.Defect

open scoped ENNReal

/-- The normalized response defect `ℳ_m(U)`. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ)
    (U : Homogenization.Book.Ch02.Domain d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ≥0∞ :=
  SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn U
    (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData M m ω U).toCoeffOn
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)

