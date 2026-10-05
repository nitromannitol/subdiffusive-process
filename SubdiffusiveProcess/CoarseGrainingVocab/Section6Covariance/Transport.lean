module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent

@[expose] public section

/-!
# Transporting a translate-`0` Section 6 estimate to every translate

Several Section 6 statements are printed only at translate `0` — for instance
the `𝓔`-cap of `p.good.scale.mathcal.E` — while their consumers read them at a
translate `z` (the excess-decay assembly needs the cap on
`goodEvent M none (n+2) z ε (s/8)`).  The two lemmas here are that step, and
nothing more: each takes the translate-`0` estimate as an explicit named
hypothesis and returns the same estimate at an arbitrary translate.

Neither lemma asserts the translate-`0` estimate; both are pure transport.  They are stated with a general
right-hand side `B` so that the exact printed bound of whichever anchor is
being transported can be supplied verbatim.

## References

* paper label `p.good.scale.mathcal.E` (`p.good.scale.mathcal.E`, at translate
  `0`), `:7601` (its use at translate `z`).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance

open MeasureTheory Homogenization

noncomputable section

variable {d : ℕ}

/-- A bound on the Section 6 error valid on the good event at translate `0`
holds on the good event at every translate. -/
theorem section6HomogenizationError_le_of_translate_zero
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {cutoff : Option ℕ} {s : ℝ}
    {L m : ℕ} {epsilon B : ℝ}
    (hzero : ∀ ν : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      ν ∈ goodEvent M cutoff m 0 epsilon s →
        section6HomogenizationError M s L m ν 0 ≤ B)
    (z : Vec d) {ω : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hω : ω ∈ goodEvent M cutoff m z epsilon s) :
    section6HomogenizationError M s L m ω z ≤ B := by
  rw [section6HomogenizationError_eq_translate_zero]
  exact hzero (translatePotentialSample z ω)
    ((mem_goodEvent_iff_translate_zero M cutoff m epsilon s z ω).mp hω)

/-- A bound on the Section 6 response valid on the good event at translate `0`
holds on the good event at every translate. -/
theorem section6Response_le_of_translate_zero
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {cutoff : Option ℕ}
    {cubeScale responseCutoff m : ℕ} {epsilon s B : ℝ} {e : Vec d}
    (hzero : ∀ ν : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      ν ∈ goodEvent M cutoff m 0 epsilon s →
        section6Response M cubeScale responseCutoff ν 0 e ≤ B)
    (z : Vec d) {ω : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hω : ω ∈ goodEvent M cutoff m z epsilon s) :
    section6Response M cubeScale responseCutoff ω z e ≤ B := by
  rw [section6Response_eq_translate_zero]
  exact hzero (translatePotentialSample z ω)
    ((mem_goodEvent_iff_translate_zero M cutoff m epsilon s z ω).mp hω)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
