module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseWindowEstimate

@[expose] public section

/-!
# Finite-cutoff accumulated-error window

This file replaces the response row in the fixed-parameter accumulated-error
window by its finite-cutoff analogue.  The shell-field and gradient rows are
unchanged, so their established Gamma-two estimates and numerical absorption
are reused verbatim.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Literal decomposition of the accumulated error at a finite response
cutoff.  Only the response summand depends on `L`. -/
theorem accumulatedError_some_holderStoppingS_eq_parts {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k : ℕ) (z : Vec d)
    (omega : Sample d) :
    accumulatedError M (some L) k z holderStoppingS omega =
      translatedCutoffAccumulatedResponseSup M L k z omega +
        translatedAccumulatedBlockSup k z holderStoppingS omega +
        (3 : ℝ) ^ (-(holderStoppingS / 8) * k) *
          supNormOn (translatedCube d (k : ℤ) z) (omega 0) +
        ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0 := by
  unfold accumulatedError translatedCutoffAccumulatedResponseSup
    translatedAccumulatedBlockSup
  simp only [Option.getD_some]

/-- The cutoff response fluctuation combined with the unchanged field and
gradient fluctuations. -/
noncomputable def cutoffAccumulatedErrorWindowFluctuation {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    (n m : ℕ) : Sample d → ℝ :=
  fun omega ↦
    cutoffAccumulatedResponseWindowFluctuation M L z n m omega +
      2 * (accumulatedFiniteFieldLowWindow z holderStoppingS n m omega +
        centeredAccumulatedFiniteFieldActiveWindow M z holderStoppingS n m omega) +
      (3 / 2 : ℝ) *
        (centeredAccumulatedGradientWindow M z n m omega +
          accumulatedGradientEnvelope m z omega)

/-- Complete cutoff one-centre reduction to the established deterministic
mean and a single combined fluctuation carrier. -/
theorem ae_sum_cutoffAccumulatedError_le_mean_add_fluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (cutoffHolderResponseRow M L j) A) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M (some L) k z holderStoppingS omega) ≤
        accumulatedErrorWindowMeanBound M A n m +
          cutoffAccumulatedErrorWindowFluctuation M L z n m omega := by
  have hresponse :=
    ae_sum_translatedCutoffAccumulatedResponseSup_le_mean_add_fluctuation
      M L z hnm hA hrow
  filter_upwards [hresponse, ae_sum_accumulatedGradientSuffix_le M z hnm]
    with omega hresp hgrad
  have hfinite :=
    sum_translatedBlockSup_add_shellZero_le_finiteFieldWindowConvolution
      z holderStoppingS_pos n m omega
  have hfieldEq := accumulatedFiniteFieldWindowConvolution_eq_low_add_active
    z holderStoppingS hnm omega
  have hfieldActive := accumulatedFiniteFieldActiveWindow_le_centered_add_mean
    M z holderStoppingS_pos (by norm_num [holderStoppingS]) hnm omega
  have hgradMean := sum_accumulatedGradientOwnRow_le_centered_add_mean
    M z n m omega
  have hcarrier :
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M (some L) k z holderStoppingS omega) ≤
        (∑ k ∈ Finset.Icc n m,
          translatedCutoffAccumulatedResponseSup M L k z omega) +
        2 * (accumulatedFiniteFieldLowWindow z holderStoppingS n m omega +
          accumulatedFiniteFieldActiveWindow z holderStoppingS n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := by
    calc
      (∑ k ∈ Finset.Icc n m,
          accumulatedError M (some L) k z holderStoppingS omega) =
        (∑ k ∈ Finset.Icc n m,
          translatedCutoffAccumulatedResponseSup M L k z omega) +
        (∑ k ∈ Finset.Icc n m,
          (translatedAccumulatedBlockSup k z holderStoppingS omega +
            (3 : ℝ) ^ (-(holderStoppingS / 8) * k) *
              supNormOn (translatedCube d (k : ℤ) z) (omega 0))) +
        (∑ k ∈ Finset.Icc n m, ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0) := by
          simp_rw [accumulatedError_some_holderStoppingS_eq_parts]
          simp_rw [Finset.sum_add_distrib]
          ring
      _ ≤ (∑ k ∈ Finset.Icc n m,
            translatedCutoffAccumulatedResponseSup M L k z omega) +
          2 * accumulatedFiniteFieldWindowConvolution
            z holderStoppingS n m omega +
          (3 / 2 : ℝ) *
            ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
              accumulatedGradientEnvelope m z omega) := by linarith
      _ = _ := by rw [hfieldEq]
  unfold cutoffAccumulatedResponseWindowMeanBound at hresp
  unfold accumulatedErrorWindowMeanBound
    cutoffAccumulatedErrorWindowFluctuation
  calc
    _ ≤ (∑ k ∈ Finset.Icc n m,
          translatedCutoffAccumulatedResponseSup M L k z omega) +
        2 * (accumulatedFiniteFieldLowWindow z holderStoppingS n m omega +
          accumulatedFiniteFieldActiveWindow z holderStoppingS n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := hcarrier
    _ ≤ ((m + 1 - n : ℕ) : ℝ) *
          (2 * (8 / holderStoppingS) *
            (IndependentSums.gammaMomentConst 2 * A)) +
          cutoffAccumulatedResponseWindowFluctuation M L z n m omega +
        2 * (accumulatedFiniteFieldLowWindow z holderStoppingS n m omega +
          (centeredAccumulatedFiniteFieldActiveWindow M z holderStoppingS n m omega +
            ((m + 1 - n : ℕ) : ℝ) *
              (IndependentSums.gammaMomentConst 2 *
                accumulatedFiniteFieldScaleBound M holderStoppingS))) +
        (3 / 2 : ℝ) *
          ((centeredAccumulatedGradientWindow M z n m omega +
              ((m + 1 - n : ℕ) : ℝ) *
                (IndependentSums.gammaMomentConst 2 *
                  accumulatedGradientOwnRowScale M)) +
            accumulatedGradientEnvelope m z omega) := by gcongr
    _ = _ := by ring

/-- The cutoff accumulated-error fluctuation has the same assembled
Gamma-two scale as the uncutoff fluctuation. -/
theorem isBigO_cutoffAccumulatedErrorWindowFluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (cutoffHolderResponseRow M L j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cutoffAccumulatedErrorWindowFluctuation M L z n m)
      (accumulatedErrorWindowFluctuationScale M A n m) := by
  let cF : ℝ := 2
  let cG : ℝ := 3 / 2
  let Rresponse : ℝ := cutoffAccumulatedResponseWindowFluctuationScale d A n m
  let Flow : ℝ := cF * (Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * fieldOneGammaDimScale M *
      (6 / (holderStoppingS / 8) ^ 2) ^ 2))
  let Factive : ℝ := cF * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedFiniteFieldScaleBound M holderStoppingS))
  let Gactive : ℝ := cG * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedGradientOwnRowScale M))
  let Gtail : ℝ := cG * accumulatedGradientEnvelopeScale M
  have hcF : 0 < cF := by unfold cF; norm_num
  have hcG : 0 < cG := by unfold cG; norm_num
  have hwindow : 0 < m + 1 - n := by omega
  have hsqrt : 0 < Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hwindow)
  have htri : 0 < Ch04.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hmoment : 0 < 1 + IndependentSums.gammaMomentConst 2 :=
    add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hRresponse : 0 < Rresponse := by
    unfold Rresponse cutoffAccumulatedResponseWindowFluctuationScale
    have hr : 0 < (responseScoreRange d : ℝ) := by
      exact_mod_cast responseScoreRange_pos d
    positivity [holderStoppingS_pos]
  have hFlow : 0 < Flow := by
    unfold Flow
    have hden : 0 < (holderStoppingS / 8) ^ 2 := by
      exact sq_pos_of_pos (by positivity [holderStoppingS_pos])
    have hsix : 0 < 6 / (holderStoppingS / 8) ^ 2 := div_pos (by norm_num) hden
    exact mul_pos hcF (mul_pos htri
      (mul_pos (mul_pos htri (fieldOneGammaDimScale_pos_stopping M))
        (sq_pos_of_pos hsix)))
  have hFactive : 0 < Factive := by
    unfold Factive
    positivity [accumulatedFiniteFieldScaleBound_pos M holderStoppingS_pos]
  have hGactive : 0 < Gactive := by
    unfold Gactive
    positivity [accumulatedGradientOwnRowScale_pos M]
  have hEnvelopeScale : 0 < accumulatedGradientEnvelopeScale M := by
    unfold accumulatedGradientEnvelopeScale
    have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
    have hlog : 0 < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    exact mul_pos (mul_pos (mul_pos hd
      IndependentSums.gammaTriangleConst_pos) (by norm_num))
      (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos)
  have hGtail : 0 < Gtail := by unfold Gtail; positivity
  let X1 : Sample d → ℝ :=
    cutoffAccumulatedResponseWindowFluctuation M L z n m
  let X2 : Sample d → ℝ := fun omega ↦ cF *
    accumulatedFiniteFieldLowWindow z holderStoppingS n m omega
  let X3 : Sample d → ℝ := fun omega ↦ cF *
    centeredAccumulatedFiniteFieldActiveWindow M z holderStoppingS n m omega
  let X4 : Sample d → ℝ := fun omega ↦ cG *
    centeredAccumulatedGradientWindow M z n m omega
  let X5 : Sample d → ℝ := fun omega ↦
    cG * accumulatedGradientEnvelope m z omega
  have hX1 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X1 Rresponse := by
    simpa only [X1, Rresponse] using
      isBigO_cutoffAccumulatedResponseWindowFluctuation M L z hnm hA hrow
  have hX2 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X2 Flow := by
    have hbase := isBigO_accumulatedFiniteFieldLowWindow M z
      holderStoppingS_pos (by norm_num [holderStoppingS]) hnm
    simpa only [X2, Flow] using hbase.const_mul hcF.le
  have hX3 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X3 Factive := by
    have hbase := isBigO_centeredAccumulatedFiniteFieldActiveWindow_le_bound
      M z holderStoppingS_pos (by norm_num [holderStoppingS]) hnm
    simpa only [X3, Factive] using hbase.const_mul hcF.le
  have hX4 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X4 Gactive := by
    have hbase := isBigO_centeredAccumulatedGradientWindow M z hnm
    simpa only [X4, Gactive] using hbase.const_mul hcG.le
  have hX5 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X5 Gtail := by
    have hbase0 := isBigOWith_gammaTwo_accumulatedGradientEnvelope M m z
    have hbase : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (accumulatedGradientEnvelope m z)
        (accumulatedGradientEnvelopeScale M) := by
      simpa [IndependentSums.IsBigO,
        abs_of_nonneg (accumulatedGradientEnvelope_nonneg m z _)] using hbase0
    simpa only [X5, Gtail] using hbase.const_mul hcG.le
  have hm1 : AEMeasurable X1 M.P.toMeasure := by
    unfold X1 cutoffAccumulatedResponseWindowFluctuation
    exact ((((measurable_cutoffAccumulatedResponseLowRows M L n).comp
      (Section6Covariance.measurable_translatePotentialSample z)).add
        ((measurable_centeredCutoffHolderResponseWindow M L n m).comp
          (Section6Covariance.measurable_translatePotentialSample z))).const_mul _).aemeasurable
  have hm2 : AEMeasurable X2 M.P.toMeasure :=
    (measurable_accumulatedFiniteFieldLowWindow z holderStoppingS n m).const_mul _ |>.aemeasurable
  have hm3 : AEMeasurable X3 M.P.toMeasure :=
    (measurable_centeredAccumulatedFiniteFieldActiveWindow
      M z holderStoppingS n m).const_mul _ |>.aemeasurable
  have hm4 : AEMeasurable X4 M.P.toMeasure :=
    (measurable_centeredAccumulatedGradientWindow M z n m).const_mul _ |>.aemeasurable
  have hm5 : AEMeasurable X5 M.P.toMeasure :=
    (aemeasurable_accumulatedGradientEnvelope M m z).const_mul _
  have h12 := isBigO_add_gammaTwo M hRresponse hFlow hX1 hX2 hm1 hm2
  have hm12 := hm1.add hm2
  have h123 := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos hRresponse hFlow)) hFactive h12 hX3 hm12 hm3
  have hm123 := hm12.add hm3
  have h1234 := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos
      (mul_pos htri (add_pos hRresponse hFlow)) hFactive))
    hGactive h123 hX4 hm123 hm4
  have hm1234 := hm123.add hm4
  have hall := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos
      (mul_pos htri (add_pos
        (mul_pos htri (add_pos hRresponse hFlow)) hFactive)) hGactive))
    hGtail h1234 hX5 hm1234 hm5
  convert hall using 1
  · funext omega
    unfold cutoffAccumulatedErrorWindowFluctuation X1 X2 X3 X4 X5 cF cG
    ring
  · unfold accumulatedErrorWindowFluctuationScale Rresponse
      cutoffAccumulatedResponseWindowFluctuationScale
      accumulatedResponseActiveWindowScale Flow Factive Gactive Gtail cF cG
    ring

/-- Exact finite-cutoff one-centre sub-Gaussian tail before the dimension-only
numerical absorption. -/
theorem measureReal_cutoffAccumulatedError_oneCenter_le_exp
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A threshold t : ℝ}
    (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (cutoffHolderResponseRow M L j) A)
    (ht : 1 ≤ t)
    (hthreshold : accumulatedErrorWindowMeanBound M A n m +
      accumulatedErrorWindowFluctuationScale M A n m * t ≤ threshold) :
    M.P.toMeasure.real {omega | threshold <
        ∑ k ∈ Finset.Icc n m,
          accumulatedError M (some L) k z holderStoppingS omega} ≤
      Real.exp (-(t ^ (2 : ℝ))) := by
  have hbig := isBigO_cutoffAccumulatedErrorWindowFluctuation
    M L z hnm hA hrow
  have htail := (IndependentSums.isBigO_gammaSigma_iff.mp hbig) ht
  have hae : {omega | threshold <
      ∑ k ∈ Finset.Icc n m,
        accumulatedError M (some L) k z holderStoppingS omega} ≤ᵐ[M.P.toMeasure]
      IndependentSums.absTailEvent
        (cutoffAccumulatedErrorWindowFluctuation M L z n m)
        (accumulatedErrorWindowFluctuationScale M A n m * t) := by
    filter_upwards [ae_sum_cutoffAccumulatedError_le_mean_add_fluctuation
      M L z hnm hA hrow] with omega hupper
    intro homega
    change threshold < ∑ k ∈ Finset.Icc n m,
      accumulatedError M (some L) k z holderStoppingS omega at homega
    unfold IndependentSums.absTailEvent IndependentSums.upperTailEvent
    dsimp only [Set.mem_setOf_eq]
    have hfluct : accumulatedErrorWindowFluctuationScale M A n m * t <
        cutoffAccumulatedErrorWindowFluctuation M L z n m omega := by
      linarith
    exact hfluct.trans_le (le_abs_self _)
  have hmeasure := MeasureTheory.measure_mono_ae hae
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
  exact hreal.trans htail

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
