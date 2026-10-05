module

public import SubdiffusiveProcess.Assumptions.AnchoredCoefficient
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-- The coefficient at a finite cutoff or at the anchored limit. -/
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ :=
  match L with
  | ⊤ => _root_.SubdiffusiveProcess.Model.aAnchored M ω
  | (n : ℕ) => _root_.SubdiffusiveProcess.Model.aCutoff M n ω.1
