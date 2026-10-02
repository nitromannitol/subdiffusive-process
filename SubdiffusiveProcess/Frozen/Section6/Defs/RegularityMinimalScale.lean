import SubdiffusiveProcess.Frozen.Section6.Defs.ErrorStoppingIndex
import SubdiffusiveProcess.Frozen.Section6.Defs.GoodStoppingIndex

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The regularity minimal scale assembled from both stopping indices. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.regularityMinimalScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cutoff : Option ℕ)
    (_alpha lambda epsilon s : ℝ) (step m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℤ :=
  max ((m : ℤ) - (errorStoppingIndex M cutoff lambda s m ω : ℤ))
      ((m : ℤ) - (goodStoppingIndex M cutoff lambda epsilon s m ω : ℤ)) +
    (step : ℤ) + 5

