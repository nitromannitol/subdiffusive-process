import SubdiffusiveProcess.Assumptions.AnchoredCoefficient
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

/-- The coefficient at a finite cutoff or at the anchored limit. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ :=
  match L with
  | ⊤ => SubdiffusiveProcess.Frozen.Assumptions.aAnchored M ω
  | (n : ℕ) => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n ω.1

