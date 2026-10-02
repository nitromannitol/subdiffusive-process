import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

open MeasureTheory
open scoped ENNReal

/-- The volume-normalized Euclidean `p = 2` fractional seminorm. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn {d : ℕ}
    (W : Set (SubdiffusiveProcess.CoarseGrainingVocab.Vec d)) (s : ℝ)
    (f : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : ℝ≥0∞ :=
  (ENNReal.ofReal s / volume W) ^ (1 / 2 : ℝ) *
    eLpNorm (SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s f) 2
      ((volume.restrict W).prod (volume.restrict W))

