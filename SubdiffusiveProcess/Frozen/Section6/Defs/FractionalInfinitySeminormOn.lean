import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
open scoped ENNReal

/-- The `p = ∞` Euclidean Hölder-quotient fractional seminorm (H2). -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.fractionalInfinitySeminormOn {d : ℕ}
    (W : Set (SubdiffusiveProcess.CoarseGrainingVocab.Vec d)) (s : ℝ)
    (f : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
    r = Homogenization.euclideanNorm (f x - f y) /
      Homogenization.euclideanNorm (x - y) ^ s})

