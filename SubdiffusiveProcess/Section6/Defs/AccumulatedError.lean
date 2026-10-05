module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-!
# Accumulated error at a scale

`accumulatedError` combines real suprema of damped response and potential
terms with a countable gradient sum. For its analytic interpretation the
supremum sets must be nonempty where needed and bounded above, and the
countable series must converge. Lean's real `sSup` and `tsum` are total;
unsummable real series have totalized sum zero. The Section 6 stopping
suppliers establish the intended bounds on the paper's positive-exponent
domain, in particular `ae_summable_accumulatedGradientLayer` in the
accumulated-error window construction. Baseline extended-score finiteness
must still be retained separately before reversing an `ENNReal.toReal` conversion.
-/

open scoped BigOperators

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The accumulated scale error, with an optional response cutoff. -/
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.accumulatedError {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (k : ℕ) (z : Vec d) (s : ℝ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
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
