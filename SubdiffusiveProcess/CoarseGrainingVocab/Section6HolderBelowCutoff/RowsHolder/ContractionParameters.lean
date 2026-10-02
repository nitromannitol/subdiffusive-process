import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ParameterAbsorption

/-!
# The block-length selection at the `s^{-2}` normalisation (D-073 / OPEN-17)

`Section6Holder.exists_holderContractionParameters` prints its contraction
clause with the manuscript's `s^{-3/2}` mean-value weight, evaluated at the
fixed Hölder scale `s = 1/4`.  The cutoff copies of the Campanato layer
(`Rows.CampanatoFull`, `Rows.IterationAppliedGate`, `Rows.GoodStep`) follow the
D-073 re-shape and print `s^{-2}` instead.  At `s = 1/4` the two weights differ
by exactly the factor

```text
  (1/4)^(-2) = 2 · (1/4)^(-3/2)   (because (1/4)^(-1/2) = 2) ,
```

which is the same identity `Section6HolderInterior.GoodStep` uses.  So the
`s^{-2}` clause is the `s^{-3/2}` clause of the *doubled* step constant, and the
selection lemma re-runs at `2 · Cstep` with no change to `k` or `C₂`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- Dimension-only selection of the block length and the `epsilon`
denominator, at the `s^{-2}` mean-value weight. -/
theorem exists_holderContractionParameters_cut (d : ℕ) (Cstep : ℝ)
    (hCstep : 0 < Cstep) :
    ∃ k : ℕ, ∃ C₂ : ℝ, 0 < k ∧ 1 ≤ C₂ ∧
      let theta := (3 : ℝ) ^ (-(1 / 4 : ℝ))
      theta ∈ Set.Ioo (0 : ℝ) 1 ∧ theta ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) ∧
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ C₂⁻¹ →
        Cstep * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            (1 / 4 : ℝ) ^ (-2 : ℝ) * epsilon) ≤ theta ^ k := by
  obtain ⟨k, C₂, hk, hC₂, hth⟩ :=
    Section6Holder.exists_holderContractionParameters d (2 * Cstep)
      (by positivity)
  obtain ⟨hthetaIoo, hthetak, hcontract⟩ := hth
  refine ⟨k, C₂, hk, hC₂, hthetaIoo, hthetak, ?_⟩
  intro epsilon hepsilon0 hepsilonC
  have hcontr := hcontract epsilon hepsilon0 hepsilonC
  have hhalf : (1 / 4 : ℝ) ^ (-1 / 2 : ℝ) = 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast (1 / 2 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpowA : (1 / 4 : ℝ) ^ (-2 : ℝ) = 2 * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [show (-2 : ℝ) = (-3 / 2 : ℝ) + (-1 / 2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num), hhalf]
    ring
  have hfirst : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  refine le_trans ?_ hcontr
  rw [hpowA]
  nlinarith [hfirst, hCstep]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder
