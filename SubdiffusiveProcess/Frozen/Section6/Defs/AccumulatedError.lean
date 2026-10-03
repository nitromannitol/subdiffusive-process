module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

open scoped BigOperators

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The accumulated scale error, with an optional response cutoff. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.accumulatedError {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cutoff : Option ℕ)
    (k : ℕ) (z : Vec d) (s : ℝ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  sSup {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
      ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧ z' - z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
          Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
            Homogenization.vecNormSq e = 1 ∧
            t = section6Response M l (min l (cutoff.getD l)) ω z' e}) 1)} +
    sSup {r : ℝ | ∃ j ≤ k,
      r = (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
        supNormOn (translatedCube d k z) (shellBlock k j ω)} +
    (3 : ℝ) ^ (-(s / 8) * k) *
      supNormOn (translatedCube d k z) (ω 0) +
    ∑' j : ℕ, if k ≤ j then
      (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d k z) (shellGradient (ω j)) else 0

