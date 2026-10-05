module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-- The finite anchored coefficient `a_L(x)/a_L(0)`. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.anchoredCutoff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (x : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : ℝ :=
  _root_.SubdiffusiveProcess.Model.aCutoff M L ω x /
    _root_.SubdiffusiveProcess.Model.aCutoff M L ω 0

