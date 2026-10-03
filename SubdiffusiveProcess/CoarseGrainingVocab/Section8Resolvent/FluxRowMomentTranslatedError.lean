module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentCellWeight
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SecondMomentBudgets

@[expose] public section

/-!
# Translated large-cube error moments for the flux row

The Section 4 large-cube anchor controls the `r = 1` and `r = 2` multiscale
errors at every translate.  This file supplies the matching measurability and
moment statements with `r` free in that two-point range.

This closes the two translated error factors `E1` and `E2`; it does not claim
a translated moment for the ellipticity factor `ahom * lambdaInv`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Measurability of the translated scalar probe maximum used in every finite
outer aggregation exponent. -/
private theorem measurable_fluxRowMoment_paperScalarProbeMax_cutoff_translate
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    (R : TriadicCube d) :
    Measurable (fun omega : Sample d ↦
      paperScalarProbeMax R
        (aCutoffFamily M L (translatePotentialSample z omega)) (ahom M L)) := by
  change Measurable (fun omega : Sample d ↦
    normalizedDefect M L (Ch02.cubeDomain R)
      (translatePotentialSequence z omega))
  exact ((measurable_normalizedDefect_potentialShellIndexSigma_Iic M L
    (Ch02.cubeDomain R)).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl).comp
        (measurable_translatePotentialSequence z)

/-- The literal translated finite-exponent paper error is measurable. -/
theorem measurable_fluxRowMoment_translatedHomogenizationErrorRandom
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ)
    (z : PaperCubeTranslate d) (s : ℝ) (r : ℕ) :
    Measurable (translatedHomogenizationErrorRandom M L K z s r) := by
  unfold translatedHomogenizationErrorRandom paperHomogenizationError
    paperHomogenizationErrorFinite paperScaleResponseAtScale
    paperMaxDescendantProbeAtScale
  apply ENNReal.continuous_rpow_const.measurable.comp
  apply Measurable.ennreal_tsum
  intro l
  apply measurable_const.mul
  apply ENNReal.continuous_rpow_const.measurable.comp
  apply ENNReal.continuous_rpow_const.measurable.comp
  exact Measurable.iSup fun R ↦
    measurable_fluxRowMoment_paperScalarProbeMax_cutoff_translate M L z R

/-- Backwards-compatible `r = 2` measurability specialization. -/
theorem measurable_fluxRowMoment_translatedHomogenizationErrorRandom_two
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ)
    (z : PaperCubeTranslate d) (s : ℝ) :
    Measurable (translatedHomogenizationErrorRandom M L K z s 2) :=
  measurable_fluxRowMoment_translatedHomogenizationErrorRandom M L K z s 2

/-- **Translated `r = 1` or `r = 2` moment root for the flux-row errors.**  This is the
literal specialization of the proved Section 4 large-cube anchor; in
particular the translate `z` and moment order `p` remain uniform binders. -/
theorem exists_fluxRowMoment_translatedError_lpnorm_bound {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (L m0 : ℕ) (s delta1 p : ℝ) (r : ℕ),
        (r = 1 ∨ r = 2) →
        0 < s → s ≤ 1 → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        L ≤ m0 →
        4 * (d : ℝ) * s⁻¹ ≤ p →
        p ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 p delta1 →
        ∀ K : ℕ, L ≤ K → ∀ z : PaperCubeTranslate d,
          paperENNRealLpNorm M.P.toMeasure p
              (translatedHomogenizationErrorRandom M L K z s r) ≤
            ENNReal.ofReal
              (C * Real.rpow s (-(1 / (r : ℝ))) * Real.sqrt delta1) := by
  obtain ⟨c, C, hc, hC, hlarge⟩ :=
    SubdiffusiveProcess.Frozen.Section4.multiscale_response_large_cubes (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M L m0 s delta1 p r hr hs hsOne hdelta hdeltaOne hLm0 hdim horder hIH
    K hLK z
  exact hlarge M L m0 s delta1 p hs hsOne hdelta hdeltaOne hLm0 hdim
    horder hIH K hLK z r hr

/-- Backwards-compatible `r = 2` moment specialization. -/
theorem exists_fluxRowMoment_translatedError_two_lpnorm_bound {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (L m0 : ℕ) (s delta1 p : ℝ),
        0 < s → s ≤ 1 → M.delta ^ 2 ≤ delta1 → delta1 < 1 → L ≤ m0 →
        4 * (d : ℝ) * s⁻¹ ≤ p →
        p ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 p delta1 →
        ∀ K : ℕ, L ≤ K → ∀ z : PaperCubeTranslate d,
          paperENNRealLpNorm M.P.toMeasure p
              (translatedHomogenizationErrorRandom M L K z s 2) ≤
            ENNReal.ofReal
              (C * Real.rpow s (-(1 / (2 : ℝ))) * Real.sqrt delta1) := by
  obtain ⟨c, C, hc, hC, hbound⟩ :=
    exists_fluxRowMoment_translatedError_lpnorm_bound (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M L m0 s delta1 p hs hsOne hdelta hdeltaOne hLm0 hdim horder hIH
    K hLK z
  exact hbound M L m0 s delta1 p 2 (Or.inr rfl) hs hsOne hdelta hdeltaOne
    hLm0 hdim horder hIH K hLK z

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
