module

public import SubdiffusiveProcess.Frozen.Section6.Defs.FractionalInfinitySeminormOn
@[expose] public section

open scoped ENNReal

/-- The paper's full underlined `W^{s,∞}` norm. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.fractionalInfinityNormOn {d : ℕ}
    (W : Set (SubdiffusiveProcess.CoarseGrainingVocab.Vec d)) (ell s : ℝ)
    (f : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → SubdiffusiveProcess.CoarseGrainingVocab.Vec d)
    (_hell : 0 < ell) : ℝ≥0∞ :=
  SubdiffusiveProcess.CoarseGrainingVocab.fractionalInfinitySeminormOn W s f +
    ENNReal.ofReal (ell ^ (-s)) *
      sSup (ENNReal.ofReal '' {r : ℝ | ∃ x ∈ W,
        r = Homogenization.euclideanNorm (f x)})

