module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodEventCap
public import SubdiffusiveProcess.Section6.CutoffRegularityGoodScales

@[expose] public section

/-!
# The finite-cutoff good-event cap for the Section 6 error

`Section6HarmonicApproximation.exists_section6HomogenizationError_le_of_goodEvent`
reads the second clause of the proved `p.good.scale.mathcal.E` and therefore
carries the binder `k ≤ L`: the uncut good event only controls the error at
scales at or below the cutoff.

The manuscript's `l.cutoff.regularity.good.scale.estimates`
instructs one to run
the harmonic-approximation argument with `p.good.scale.mathcal.E` replaced by
`p.cutoff.regularity.good.scales`.  In Lean that replacement happens exactly
here: the **proved** frozen anchor
`SubdiffusiveProcess.Section6.cutoff_regularity_good_scales` has, as its fifth conjunct,

```text
  indicatorValue (goodEvent M (some L) m z epsilon s)
      (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon
```

for **every** `L` and `m`, with no relation imposed between them.  Specialising
to `epsilon = 1` at the rescaled parameter `s / 8` yields the cutoff companion
of the uncut cap, with the binder `k ≤ L` deleted.

The relevant good-event condition is `e.cutoff.regularity.good.E.epsilon`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- **The finite-cutoff good-event cap.**  On the cutoff good event
`𝒢^{(L)}_{k,z}(1, s/8)` the local Section 6 error is bounded by a dimension-only
constant, for **every** pair `(L, k)`: the uncut cap's binder `k ≤ L` is gone.

This is `e.cutoff.regularity.good.E.epsilon`, i.e. the fifth conjunct of the
proved `SubdiffusiveProcess.Section6.cutoff_regularity_good_scales`, at `epsilon = 1`. -/
theorem exists_section6HomogenizationError_le_of_cutoffGoodEvent :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L k : ℕ,
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, ∀ z : Vec d,
        omega ∈ goodEvent M (some L) k z 1 (s / 8) →
          section6HomogenizationError M (s / 8) L k omega z ≤ C := by
  obtain ⟨C, hC, hcut⟩ := _root_.SubdiffusiveProcess.Section6.cutoff_regularity_good_scales d
  refine ⟨C, hC, ?_⟩
  intro M s hs L k omega z homega
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdelta2 : (0 : ℝ) < M.delta ^ 2 := pow_pos hdelta 2
  have hs0 : 0 < s := (mul_pos (by norm_num) hdelta2).trans_le hs.1
  have hs8 : 0 < s / 8 := by positivity
  have htRange : s / 8 ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hepsRange : (1 : ℝ) ∈ Set.Icc ((s / 8)⁻¹ * M.delta ^ 2) 1 := by
    refine ⟨?_, le_rfl⟩
    rw [inv_mul_le_iff₀ hs8]
    have : 512 * M.delta ^ 2 ≤ s := hs.1
    linarith
  have hcap := ((hcut M L).2.2.2.2 (s / 8) htRange 1 hepsRange k z omega).2
  rw [Section6ExcessDecay.indicatorValue_of_mem homega] at hcap
  simpa using hcap

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
