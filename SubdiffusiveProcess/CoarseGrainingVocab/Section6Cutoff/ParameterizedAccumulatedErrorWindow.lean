module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseWindowEstimate

@[expose] public section

/-!
# Parameterized finite-cutoff accumulated-error window

This module combines the arbitrary-`s` cutoff response window with the already
parameterized shell-field window and the unchanged gradient suffix.  It keeps
the exact mean and Gamma-two scales visible for the cutoff ladder's numerical
absorption.
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
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Literal decomposition of the finite-cutoff accumulated error at arbitrary
exponent `s`. -/
theorem accumulatedError_some_eq_parameterized_parts {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ) (z : Vec d)
    (s : ℝ) (omega : Sample d) :
    accumulatedError M (some L) k z s omega =
      translatedCutoffParameterizedAccumulatedResponseSup M L s k z omega +
        translatedAccumulatedBlockSup k z s omega +
        (3 : ℝ) ^ (-(s / 8) * k) *
          supNormOn (translatedCube d (k : ℤ) z) (omega 0) +
        ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0 := by
  unfold accumulatedError
    translatedCutoffParameterizedAccumulatedResponseSup
    translatedAccumulatedBlockSup
  simp only [Option.getD_some]

noncomputable def cutoffParameterizedAccumulatedErrorWindowFluctuation
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ)
    (z : Vec d) (n m : ℕ) : Sample d → ℝ :=
  fun omega =>
    cutoffParameterizedAccumulatedResponseWindowFluctuation M L s z n m omega +
      2 * (accumulatedFiniteFieldLowWindow z s n m omega +
        centeredAccumulatedFiniteFieldActiveWindow M z s n m omega) +
      (3 / 2 : ℝ) *
        (centeredAccumulatedGradientWindow M z n m omega +
          accumulatedGradientEnvelope m z omega)

def cutoffParameterizedAccumulatedErrorWindowMeanBound {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s A : ℝ)
    (n m : ℕ) : ℝ :=
  ((m + 1 - n : ℕ) : ℝ) *
    (2 * (8 / s) * (IndependentSums.gammaMomentConst 2 * A) +
      2 * (IndependentSums.gammaMomentConst 2 *
        accumulatedFiniteFieldScaleBound M s) +
      (3 / 2 : ℝ) *
        (IndependentSums.gammaMomentConst 2 * accumulatedGradientOwnRowScale M))

def cutoffParameterizedAccumulatedErrorWindowFluctuationScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s A : ℝ)
    (n m : ℕ) : ℝ :=
  let T := Ch04.gammaTriangleConst 2
  let Rresponse :=
    cutoffParameterizedAccumulatedResponseWindowFluctuationScale d s A n m
  let Flow := 2 * (Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * fieldOneGammaDimScale M *
      (6 / (s / 8) ^ 2) ^ 2))
  let Factive := 2 * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedFiniteFieldScaleBound M s))
  let Gactive := (3 / 2 : ℝ) *
    (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) *
          accumulatedGradientOwnRowScale M))
  let Gtail := (3 / 2 : ℝ) * accumulatedGradientEnvelopeScale M
  T * (T * (T * (T * (Rresponse + Flow) + Factive) + Gactive) + Gtail)

/-- Complete arbitrary-`s` one-centre reduction to a deterministic linear
mean and one fluctuation carrier. -/
theorem ae_sum_cutoffParameterizedAccumulatedError_le_mean_add_fluctuation
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M (some L) k z s omega) ≤
        cutoffParameterizedAccumulatedErrorWindowMeanBound M s A n m +
          cutoffParameterizedAccumulatedErrorWindowFluctuation
            M L s z n m omega := by
  have hresponse :=
    ae_sum_translatedCutoffParameterizedAccumulatedResponseSup_le_mean_add_fluctuation
      M L hs hs1 z hnm hA hrow
  have hs8 : s / 8 ≤ 1 := by linarith
  filter_upwards [hresponse, ae_sum_accumulatedGradientSuffix_le M z hnm]
    with omega hresp hgrad
  have hfinite :=
    sum_translatedBlockSup_add_shellZero_le_finiteFieldWindowConvolution
      z hs n m omega
  have hfieldEq := accumulatedFiniteFieldWindowConvolution_eq_low_add_active
    z s hnm omega
  have hfieldActive := accumulatedFiniteFieldActiveWindow_le_centered_add_mean
    M z hs hs8 hnm omega
  have hgradMean := sum_accumulatedGradientOwnRow_le_centered_add_mean
    M z n m omega
  have hcarrier :
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M (some L) k z s omega) ≤
        (∑ k ∈ Finset.Icc n m,
          translatedCutoffParameterizedAccumulatedResponseSup
            M L s k z omega) +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
          accumulatedFiniteFieldActiveWindow z s n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := by
    calc
      (∑ k ∈ Finset.Icc n m,
          accumulatedError M (some L) k z s omega) =
        (∑ k ∈ Finset.Icc n m,
          translatedCutoffParameterizedAccumulatedResponseSup
            M L s k z omega) +
        (∑ k ∈ Finset.Icc n m,
          (translatedAccumulatedBlockSup k z s omega +
            (3 : ℝ) ^ (-(s / 8) * k) *
              supNormOn (translatedCube d (k : ℤ) z) (omega 0))) +
        (∑ k ∈ Finset.Icc n m, ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0) := by
          simp_rw [accumulatedError_some_eq_parameterized_parts]
          simp_rw [Finset.sum_add_distrib]
          ring
      _ ≤ (∑ k ∈ Finset.Icc n m,
            translatedCutoffParameterizedAccumulatedResponseSup
              M L s k z omega) +
          2 * accumulatedFiniteFieldWindowConvolution z s n m omega +
          (3 / 2 : ℝ) *
            ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
              accumulatedGradientEnvelope m z omega) := by linarith
      _ = _ := by rw [hfieldEq]
  unfold cutoffParameterizedAccumulatedResponseWindowMeanBound at hresp
  unfold cutoffParameterizedAccumulatedErrorWindowMeanBound
    cutoffParameterizedAccumulatedErrorWindowFluctuation
  calc
    _ ≤ (∑ k ∈ Finset.Icc n m,
          translatedCutoffParameterizedAccumulatedResponseSup
            M L s k z omega) +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
          accumulatedFiniteFieldActiveWindow z s n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := hcarrier
    _ ≤ ((m + 1 - n : ℕ) : ℝ) *
          (2 * (8 / s) * (IndependentSums.gammaMomentConst 2 * A)) +
          cutoffParameterizedAccumulatedResponseWindowFluctuation
            M L s z n m omega +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
          (centeredAccumulatedFiniteFieldActiveWindow M z s n m omega +
            ((m + 1 - n : ℕ) : ℝ) *
              (IndependentSums.gammaMomentConst 2 *
                accumulatedFiniteFieldScaleBound M s))) +
        (3 / 2 : ℝ) *
          ((centeredAccumulatedGradientWindow M z n m omega +
              ((m + 1 - n : ℕ) : ℝ) *
                (IndependentSums.gammaMomentConst 2 *
                  accumulatedGradientOwnRowScale M)) +
            accumulatedGradientEnvelope m z omega) := by gcongr
    _ = _ := by ring

/-- The arbitrary-`s` finite-cutoff accumulated-error fluctuation is
Gamma-two at the exact scale assembled from the response, field, and gradient
components. -/
theorem isBigO_cutoffParameterizedAccumulatedErrorWindowFluctuation
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m)
      (cutoffParameterizedAccumulatedErrorWindowFluctuationScale
        M s A n m) := by
  let cF : ℝ := 2
  let cG : ℝ := 3 / 2
  let Rresponse : ℝ :=
    cutoffParameterizedAccumulatedResponseWindowFluctuationScale d s A n m
  let Flow : ℝ := cF * (Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * fieldOneGammaDimScale M *
      (6 / (s / 8) ^ 2) ^ 2))
  let Factive : ℝ := cF * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedFiniteFieldScaleBound M s))
  let Gactive : ℝ := cG * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedGradientOwnRowScale M))
  let Gtail : ℝ := cG * accumulatedGradientEnvelopeScale M
  have hs8 : s / 8 ≤ 1 := by linarith
  have hcF : 0 < cF := by unfold cF; norm_num
  have hcG : 0 < cG := by unfold cG; norm_num
  have hwindow : 0 < m + 1 - n := by omega
  have hsqrt : 0 < Real.sqrt ((m + 1 - n : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hwindow)
  have htri : 0 < Ch04.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hmoment : 0 < 1 + IndependentSums.gammaMomentConst 2 :=
    add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hRresponse : 0 < Rresponse := by
    unfold Rresponse
      cutoffParameterizedAccumulatedResponseWindowFluctuationScale
    have hr : 0 < (responseScoreRange d : ℝ) := by
      exact_mod_cast responseScoreRange_pos d
    positivity
  have hFlow : 0 < Flow := by
    unfold Flow
    have hden : 0 < (s / 8) ^ 2 := sq_pos_of_pos (by positivity)
    have hsix : 0 < 6 / (s / 8) ^ 2 := div_pos (by norm_num) hden
    exact mul_pos hcF (mul_pos htri
      (mul_pos (mul_pos htri (fieldOneGammaDimScale_pos_stopping M))
        (sq_pos_of_pos hsix)))
  have hFactive : 0 < Factive := by
    unfold Factive
    positivity [accumulatedFiniteFieldScaleBound_pos M hs]
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
    cutoffParameterizedAccumulatedResponseWindowFluctuation M L s z n m
  let X2 : Sample d → ℝ := fun omega => cF *
    accumulatedFiniteFieldLowWindow z s n m omega
  let X3 : Sample d → ℝ := fun omega => cF *
    centeredAccumulatedFiniteFieldActiveWindow M z s n m omega
  let X4 : Sample d → ℝ := fun omega => cG *
    centeredAccumulatedGradientWindow M z n m omega
  let X5 : Sample d → ℝ := fun omega =>
    cG * accumulatedGradientEnvelope m z omega
  have hX1 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X1 Rresponse := by
    simpa only [X1, Rresponse] using!
      isBigO_cutoffParameterizedAccumulatedResponseWindowFluctuation
        M L hs hs1 z hnm hA hrow
  have hX2 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X2 Flow := by
    have hbase := isBigO_accumulatedFiniteFieldLowWindow M z hs hs8 hnm
    simpa only [X2, Flow] using! hbase.const_mul hcF.le
  have hX3 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X3 Factive := by
    have hbase := isBigO_centeredAccumulatedFiniteFieldActiveWindow_le_bound
      M z hs hs8 hnm
    simpa only [X3, Factive] using! hbase.const_mul hcF.le
  have hX4 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X4 Gactive := by
    have hbase := isBigO_centeredAccumulatedGradientWindow M z hnm
    simpa only [X4, Gactive] using! hbase.const_mul hcG.le
  have hX5 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X5 Gtail := by
    have hbase0 := isBigOWith_gammaTwo_accumulatedGradientEnvelope M m z
    have hbase : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (accumulatedGradientEnvelope m z)
        (accumulatedGradientEnvelopeScale M) := by
      simpa [IndependentSums.IsBigO,
        abs_of_nonneg (accumulatedGradientEnvelope_nonneg m z _)] using! hbase0
    simpa only [X5, Gtail] using! hbase.const_mul hcG.le
  have hm1 : AEMeasurable X1 M.P.toMeasure := by
    unfold X1 cutoffParameterizedAccumulatedResponseWindowFluctuation
    exact ((((measurable_cutoffParameterizedAccumulatedResponseLowRows
      M L s n).comp
        (Section6Covariance.measurable_translatePotentialSample z)).add
      ((measurable_centeredCutoffParameterizedResponseWindow M L s n m).comp
        (Section6Covariance.measurable_translatePotentialSample z))).const_mul _).aemeasurable
  have hm2 : AEMeasurable X2 M.P.toMeasure :=
    (measurable_accumulatedFiniteFieldLowWindow z s n m).const_mul _
      |>.aemeasurable
  have hm3 : AEMeasurable X3 M.P.toMeasure :=
    (measurable_centeredAccumulatedFiniteFieldActiveWindow M z s n m).const_mul _
      |>.aemeasurable
  have hm4 : AEMeasurable X4 M.P.toMeasure :=
    (measurable_centeredAccumulatedGradientWindow M z n m).const_mul _
      |>.aemeasurable
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
    unfold cutoffParameterizedAccumulatedErrorWindowFluctuation
      X1 X2 X3 X4 X5 cF cG
    ring
  · rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
