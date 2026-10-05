module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support

@[expose] public section

/-- The tail coefficient `b_{L,m}`. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.tailCoefficient {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (x : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : ℝ :=
  SubdiffusiveProcess.CoarseGrainingVocab.ahom M (min m L) *
    (_root_.SubdiffusiveProcess.Model.aCutoff M L ω x /
      _root_.SubdiffusiveProcess.Model.aCutoff M (min m L) ω x)

