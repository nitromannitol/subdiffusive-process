module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-- The finite anchored coefficient `a_L(x)/a_L(0)`. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.anchoredCutoff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : ℝ :=
  SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x /
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω 0

