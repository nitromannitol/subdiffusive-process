module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support

@[expose] public section

/-- The tail coefficient `b_{L,m}`. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.tailCoefficient {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : ℝ :=
  SubdiffusiveProcess.CoarseGrainingVocab.ahom M (min m L) *
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (min m L) ω x)

