module

public import SubdiffusiveProcess.Section6SumErrors.WindowCarriers

@[expose] public section

/-!
# WindowFluctuation

Gaussian tails of the six accumulated-error window fluctuation carriers and the resulting fixed-center upper tail.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

theorem isBigO_accumulatedErrorWindowFluctuation (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Homogenization.Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) ((holderResponseRow s) M j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      ((accumulatedErrorWindowFluctuation s) M z n m)
      ((accumulatedErrorWindowFluctuationScale s) M A n m) := by
  let cR : ℝ := 2 * (8 / s)
  let cF : ℝ := 2
  let cG : ℝ := 3 / 2
  let Rlow : ℝ := cR *
    (Ch04.gammaTriangleConst 2 * ((8 / s) * A))
  let Ractive : ℝ := cR * accumulatedResponseActiveWindowScale d A n m
  let Flow : ℝ := cF * (Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * fieldOneGammaDimScale M *
      (24 / (s / 8) ^ 3)))
  let Factive : ℝ := cF * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedFiniteFieldScaleBound M s))
  let Gactive : ℝ := cG * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedGradientOwnRowScale M))
  let Gtail : ℝ := cG * accumulatedGradientEnvelopeScale M
  have hcR : 0 < cR := by unfold cR; positivity [hs]
  have hcF : 0 < cF := by unfold cF; norm_num
  have hcG : 0 < cG := by unfold cG; norm_num
  have hwindow : 0 < m + 1 - n := by omega
  have hsqrt : 0 < Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hwindow)
  have htri : 0 < Ch04.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
    (gammaSigmaIndependentSumConst_two_pos)
  have hmoment : 0 < 1 + IndependentSums.gammaMomentConst 2 :=
    add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hRlow : 0 < Rlow := by
    unfold Rlow
    exact mul_pos hcR (mul_pos htri
      (mul_pos (by positivity [hs]) hA))
  have hRactive : 0 < Ractive := by
    unfold Ractive accumulatedResponseActiveWindowScale
    have hr : 0 < (responseScoreRange d : ℝ) := by
      exact_mod_cast responseScoreRange_pos d
    positivity
  have hFlow : 0 < Flow := by
    unfold Flow
    positivity [fieldOneGammaDimScale_pos_stopping M]
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
  let X1 : Sample d → ℝ := fun omega ↦ cR *
    (accumulatedResponseLowRows s) M n (translatePotentialSample z omega)
  let X2 : Sample d → ℝ := fun omega ↦ cR *
    (centeredHolderResponseWindow s) M n m (translatePotentialSample z omega)
  let X3 : Sample d → ℝ := fun omega ↦ cF *
    accumulatedFiniteFieldLowWindow z s n m omega
  let X4 : Sample d → ℝ := fun omega ↦ cF *
    centeredAccumulatedFiniteFieldActiveWindow M z s n m omega
  let X5 : Sample d → ℝ := fun omega ↦ cG *
    centeredAccumulatedGradientWindow M z n m omega
  let X6 : Sample d → ℝ := fun omega ↦ cG * accumulatedGradientEnvelope m z omega
  have hX1 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X1 Rlow := by
    have hbase := isBigO_comp_translatePotentialSample M z
      ((isBigO_accumulatedResponseLowRows s hs hs1) M n hA hrow)
    simpa only [X1, Rlow] using! hbase.const_mul hcR.le
  have hX2 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X2 Ractive := by
    have hbase0 := (isBigO_centeredHolderResponseWindow s) M
      (responseScoreRange d) n m (responseScoreRange_pos d) hnm
      ((columnsIndep_holderResponseRowArray s) M) hA hrow
    have hbase := isBigO_comp_translatePotentialSample M z hbase0
    simpa only [X2, Ractive, accumulatedResponseActiveWindowScale] using!
      hbase.const_mul hcR.le
  have hX3 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X3 Flow := by
    have hbase := SubdiffusiveProcess.Section6SumErrors.isBigO_fieldLowWindow M z
      hs (by linarith) hnm
    simpa only [X3, Flow] using! hbase.const_mul hcF.le
  have hX4 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X4 Factive := by
    have hbase := isBigO_centeredAccumulatedFiniteFieldActiveWindow_le_bound
      M z hs (by linarith) hnm
    simpa only [X4, Factive] using! hbase.const_mul hcF.le
  have hX5 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X5 Gactive := by
    have hbase := isBigO_centeredAccumulatedGradientWindow M z hnm
    simpa only [X5, Gactive] using! hbase.const_mul hcG.le
  have hX6 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X6 Gtail := by
    have hbase0 := isBigOWith_gammaTwo_accumulatedGradientEnvelope M m z
    have hbase : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (accumulatedGradientEnvelope m z)
        (accumulatedGradientEnvelopeScale M) := by
      simpa [IndependentSums.IsBigO,
        abs_of_nonneg (accumulatedGradientEnvelope_nonneg m z _)] using! hbase0
    simpa only [X6, Gtail] using! hbase.const_mul hcG.le
  have hm1 : AEMeasurable X1 M.P.toMeasure := by
    exact (((measurable_accumulatedResponseLowRows s) M n).comp
      (Section6Covariance.measurable_translatePotentialSample z)).const_mul _ |>.aemeasurable
  have hm2 : AEMeasurable X2 M.P.toMeasure := by
    exact (((measurable_centeredHolderResponseWindow s) M n m).comp
      (Section6Covariance.measurable_translatePotentialSample z)).const_mul _ |>.aemeasurable
  have hm3 : AEMeasurable X3 M.P.toMeasure :=
    (measurable_accumulatedFiniteFieldLowWindow z s n m).const_mul _ |>.aemeasurable
  have hm4 : AEMeasurable X4 M.P.toMeasure :=
    (measurable_centeredAccumulatedFiniteFieldActiveWindow M z s n m).const_mul _ |>.aemeasurable
  have hm5 : AEMeasurable X5 M.P.toMeasure :=
    (measurable_centeredAccumulatedGradientWindow M z n m).const_mul _ |>.aemeasurable
  have hm6 : AEMeasurable X6 M.P.toMeasure :=
    (aemeasurable_accumulatedGradientEnvelope M m z).const_mul _
  have h12 := isBigO_add_gammaTwo M hRlow hRactive hX1 hX2 hm1 hm2
  have hm12 := hm1.add hm2
  have h123 := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos hRlow hRactive)) hFlow h12 hX3 hm12 hm3
  have hm123 := hm12.add hm3
  have h1234 := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos (mul_pos htri (add_pos hRlow hRactive)) hFlow))
    hFactive h123 hX4 hm123 hm4
  have hm1234 := hm123.add hm4
  have h12345 := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos
      (mul_pos htri (add_pos (mul_pos htri (add_pos hRlow hRactive)) hFlow))
      hFactive)) hGactive h1234 hX5 hm1234 hm5
  have hm12345 := hm1234.add hm5
  have hall := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos
      (mul_pos htri (add_pos
        (mul_pos htri (add_pos (mul_pos htri (add_pos hRlow hRactive)) hFlow))
        hFactive)) hGactive)) hGtail h12345 hX6 hm12345 hm6
  convert hall using 1
  · funext omega
    unfold accumulatedErrorWindowFluctuation X1 X2 X3 X4 X5 X6 cR cF cG
    ring
  · rfl

theorem measureReal_accumulatedError_oneCenter_le_exp (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Homogenization.Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A threshold t : ℝ}
    (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) ((holderResponseRow s) M j) A)
    (B : ℝ) (hmean : ∀ j : ℕ, ∫ omega, holderResponseRow s M j omega ∂M.P.toMeasure ≤ B)
    (ht : 1 ≤ t)
    (hthreshold : (accumulatedErrorWindowMeanBound s) M B n m +
      (accumulatedErrorWindowFluctuationScale s) M A n m * t ≤ threshold) :
    M.P.toMeasure.real {omega | threshold <
        ∑ k ∈ Finset.Icc n m,
          accumulatedError M none k z s omega} ≤
      Real.exp (-(t ^ (2 : ℝ))) := by
  have hbig := (isBigO_accumulatedErrorWindowFluctuation s hs hs1) M z hnm hA hrow
  have htail := (IndependentSums.isBigO_gammaSigma_iff.mp hbig) ht
  have hae : {omega | threshold <
      ∑ k ∈ Finset.Icc n m,
        accumulatedError M none k z s omega} ≤ᵐ[M.P.toMeasure]
      IndependentSums.absTailEvent
        ((accumulatedErrorWindowFluctuation s) M z n m)
        ((accumulatedErrorWindowFluctuationScale s) M A n m * t) := by
    filter_upwards [(ae_sum_accumulatedError_le_mean_add_fluctuation s hs hs1)
      M z hnm B hmean] with omega hupper
    intro homega
    change threshold < ∑ k ∈ Finset.Icc n m,
      accumulatedError M none k z s omega at homega
    unfold IndependentSums.absTailEvent IndependentSums.upperTailEvent
    dsimp only [Set.mem_ofPred_eq]
    have hfluct : (accumulatedErrorWindowFluctuationScale s) M A n m * t <
        (accumulatedErrorWindowFluctuation s) M z n m omega := by linarith
    exact hfluct.trans_le (le_abs_self _)
  have hmeasure := MeasureTheory.measure_mono_ae hae
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
  exact hreal.trans htail

end
end SubdiffusiveProcess.Section6SumErrors.Response
