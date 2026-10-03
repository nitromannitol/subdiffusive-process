module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GoodDensityTranslation

@[expose] public section

/-!
# Translation of finite-cutoff good-scale density

The cutoff density estimate is uniform in the deterministic cutoff.  This
module transports its origin-centred conclusion to arbitrary deterministic
centres with no change in constants.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Source-form origin-centred cutoff density conclusion. -/
def CutoffDensityOfGoodScalesInput (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ L : ℕ, ∀ s theta epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| ≤ theta →
      ∀ m0 K : ℕ,
        M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
            if omega ∈ goodEvent M (some L) m 0 epsilon s then
              (1 : ℝ) else 0) / (K + 1) ≤ 1 - theta} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
            (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1)))

theorem cutoffGoodDensityFailure_eq_preimage_translate {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s theta epsilon : ℝ) (z : Vec d) (m0 K : ℕ) :
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | (∑ m ∈ Finset.Icc m0 (m0 + K),
        if omega ∈ goodEvent M (some L) m z epsilon s then (1 : ℝ) else 0) /
          (K + 1) ≤ 1 - theta} =
      translatePotentialSample z ⁻¹'
        {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | (∑ m ∈ Finset.Icc m0 (m0 + K),
          if omega ∈ goodEvent M (some L) m 0 epsilon s then
            (1 : ℝ) else 0) / (K + 1) ≤ 1 - theta} := by
  ext omega
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  have hsum : (∑ m ∈ Finset.Icc m0 (m0 + K),
        if omega ∈ goodEvent M (some L) m z epsilon s then (1 : ℝ) else 0) =
      ∑ m ∈ Finset.Icc m0 (m0 + K),
        if translatePotentialSample z omega ∈
            goodEvent M (some L) m 0 epsilon s then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro m _hm
    rw [if_congr
      (mem_goodEvent_iff_translate_zero M (some L) m epsilon s z omega) rfl rfl]
  rw [hsum]

theorem cutoffDensityOfGoodScalesInput_translated {d : ℕ}
    (hDensity : CutoffDensityOfGoodScalesInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ L : ℕ, ∀ s theta epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| ≤ theta →
      ∀ z : Vec d, ∀ m0 K : ℕ,
        M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
            if omega ∈ goodEvent M (some L) m z epsilon s then
              (1 : ℝ) else 0) / (K + 1) ≤ 1 - theta} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
            (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) := by
  obtain ⟨C, hC, hbase⟩ := hDensity
  refine ⟨C, hC, ?_⟩
  intro M L s theta epsilon hs htheta hepsilon hsmall z m0 K
  rw [cutoffGoodDensityFailure_eq_preimage_translate
    M L s theta epsilon z m0 K, measure_preimage_translatePotentialSample]
  exact hbase M L s theta epsilon hs htheta hepsilon hsmall m0 K

theorem measure_translated_cutoffBadScaleCount_large_le {d : ℕ}
    (hDensity : CutoffDensityOfGoodScalesInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ L : ℕ, ∀ s lambda epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → lambda ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| ≤ lambda / 2 →
      ∀ z : Vec d, ∀ m0 K : ℕ,
        M.P.toMeasure {omega |
            lambda * K < ∑ m ∈ Finset.Icc m0 (m0 + K),
              (1 - if omega ∈ goodEvent M (some L) m z epsilon s then
                (1 : ℝ) else 0)} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
            (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) := by
  obtain ⟨C, hC, htranslated⟩ :=
    cutoffDensityOfGoodScalesInput_translated hDensity
  refine ⟨C, hC, ?_⟩
  intro M L s lambda epsilon hs hlambda hepsilon hsmall z m0 K
  have hhalf : lambda / 2 ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by linarith [hlambda.1], by linarith [hlambda.2]⟩
  calc
    M.P.toMeasure {omega |
        lambda * K < ∑ m ∈ Finset.Icc m0 (m0 + K),
          (1 - if omega ∈ goodEvent M (some L) m z epsilon s then
            (1 : ℝ) else 0)} ≤
      M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
          if omega ∈ goodEvent M (some L) m z epsilon s then
            (1 : ℝ) else 0) / (K + 1) ≤ 1 - lambda / 2} := by
      apply measure_mono
      intro omega homega
      exact goodDensityFailure_of_badCount_large
        (fun m ↦ omega ∈ goodEvent M (some L) m z epsilon s)
        lambda hlambda.1 hlambda.2 m0 K homega
    _ ≤ ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
          (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) :=
      htranslated M L s (lambda / 2) epsilon hs hhalf hepsilon hsmall z m0 K

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
