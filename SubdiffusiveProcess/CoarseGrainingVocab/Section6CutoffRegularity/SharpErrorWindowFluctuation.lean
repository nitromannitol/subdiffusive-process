module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedAccumulatedErrorWindow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpFieldLowWindow

@[expose] public section

/-!
# The accumulated-error window fluctuation at a sharp field-low scale

`Section6Cutoff.cutoffParameterizedAccumulatedErrorWindowFluctuationScale` hard
codes the field-low slot at the lossy value
`2 * (T * (T * fieldOneGammaDimScale M * (6 / (s / 8) ^ 2) ^ 2))`, i.e. at
`≍ delta * s ^ (-4)`.  Every other slot of that definition already sits inside
the printed `delta * s ^ (-7 / 2)`, so the field-low slot is the only obstruction
to `e.cutoff.regularity.error.average`.

This module rebuilds the proved assembly with the field-low slot left as a
parameter `FlowRaw`, taken together with its `Gamma`-two hypothesis.  Nothing
else in the assembly touches the low window, so the generic proof is the proved
proof verbatim with one `have` replaced by a hypothesis.  The *carrier*
`cutoffParameterizedAccumulatedErrorWindowFluctuation` is literally unchanged,
so the proved sharp-mean chain of `SharpMeanAccumulated.lean` composes with the
result without modification.

`cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen_eq` records that
the generic scale reduces to the proved one at the proved `FlowRaw`, which is
what makes this a generalization rather than a restatement.

`isBigO_cutoffParameterizedAccumulatedErrorWindowFluctuation_sharp` then
instantiates it at the sharp low-window scale of `SharpFieldLowWindow.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The proved fluctuation scale with the field-low slot left free.  The nesting
`T * (T * (T * (T * (Rresponse + Flow) + Factive) + Gactive) + Gtail)` is exactly
that of `Section6Cutoff.cutoffParameterizedAccumulatedErrorWindowFluctuationScale`;
only `Flow` is a parameter. -/
def cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s A : ℝ) (n m : ℕ)
    (FlowRaw : ℝ) : ℝ :=
  let T := Ch04.gammaTriangleConst 2
  let Rresponse :=
    cutoffParameterizedAccumulatedResponseWindowFluctuationScale d s A n m
  let Flow := 2 * FlowRaw
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

/-- At the proved field-low scale the generic scale is the proved scale. -/
theorem cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s A : ℝ) (n m : ℕ) :
    cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
        (Ch04.gammaTriangleConst 2 *
          (Ch04.gammaTriangleConst 2 * fieldOneGammaDimScale M *
            (6 / (s / 8) ^ 2) ^ 2)) =
      cutoffParameterizedAccumulatedErrorWindowFluctuationScale M s A n m := by
  unfold cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
    cutoffParameterizedAccumulatedErrorWindowFluctuationScale
  ring

/-- The proved assembly, with the field-low slot supplied as a hypothesis. -/
theorem isBigO_cutoffParameterizedAccumulatedErrorWindowFluctuation_gen
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    {FlowRaw : ℝ} (hFlowRaw : 0 < FlowRaw)
    (hFlowBigO : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (accumulatedFiniteFieldLowWindow z s n m) FlowRaw) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m)
      (cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
        M s A n m FlowRaw) := by
  let cF : ℝ := 2
  let cG : ℝ := 3 / 2
  let Rresponse : ℝ :=
    cutoffParameterizedAccumulatedResponseWindowFluctuationScale d s A n m
  let Flow : ℝ := cF * FlowRaw
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
  have hFlow : 0 < Flow := mul_pos hcF hFlowRaw
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
    simpa only [X1, Rresponse] using
      isBigO_cutoffParameterizedAccumulatedResponseWindowFluctuation
        M L hs hs1 z hnm hA hrow
  have hX2 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X2 Flow := by
    simpa only [X2, Flow] using hFlowBigO.const_mul hcF.le
  have hX3 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X3 Factive := by
    have hbase := isBigO_centeredAccumulatedFiniteFieldActiveWindow_le_bound
      M z hs hs8 hnm
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

/-- Strict positivity of the generic fluctuation scale. -/
theorem cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen_pos
    {d : ℕ} [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s A : ℝ}
    (hs : 0 < s) (hA : 0 < A) {n m : ℕ} (hnm : n ≤ m)
    {FlowRaw : ℝ} (hFlowRaw : 0 < FlowRaw) :
    0 < cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
      M s A n m FlowRaw := by
  unfold cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
  have htri : 0 < Ch04.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hmoment : 0 < 1 + IndependentSums.gammaMomentConst 2 :=
    add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hwindow : 0 < m + 1 - n := by omega
  have hsqrt : 0 < Real.sqrt ((m + 1 - n : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hwindow)
  have hRresponse :
      0 < cutoffParameterizedAccumulatedResponseWindowFluctuationScale d s A n m := by
    unfold cutoffParameterizedAccumulatedResponseWindowFluctuationScale
    have hr : 0 < (responseScoreRange d : ℝ) := by
      exact_mod_cast responseScoreRange_pos d
    positivity
  have hFactive : 0 < 2 * (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) *
          accumulatedFiniteFieldScaleBound M s)) := by
    positivity [accumulatedFiniteFieldScaleBound_pos M hs]
  have hGactive : 0 < (3 / 2 : ℝ) * (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) *
          accumulatedGradientOwnRowScale M)) := by
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
  have hGtail : 0 < (3 / 2 : ℝ) * accumulatedGradientEnvelopeScale M := by
    positivity
  have h1 : 0 < cutoffParameterizedAccumulatedResponseWindowFluctuationScale d s A n m
      + 2 * FlowRaw := by linarith
  have h2 := mul_pos htri h1
  have h3 : 0 < Ch04.gammaTriangleConst 2 *
      (cutoffParameterizedAccumulatedResponseWindowFluctuationScale d s A n m
        + 2 * FlowRaw) + 2 * (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) *
          accumulatedFiniteFieldScaleBound M s)) := by linarith
  have h4 := mul_pos htri h3
  have h5 := add_pos h4 hGactive
  have h6 := mul_pos htri h5
  have h7 := add_pos h6 hGtail
  exact mul_pos htri h7

/-- Strict positivity of the sharp field-low scale, needed to feed the generic
assembly. -/
theorem sharpFieldLowColumnScaleSum_pos {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ} (hs : 0 < s) :
    0 < sharpFieldLowColumnScaleSum M s := by
  unfold sharpFieldLowColumnScaleSum
  have ht : (0 : ℝ) < s / 8 := by positivity
  have hD := fieldOneGammaDimScale_pos_stopping M
  have htri : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hrest : (0 : ℝ) < 32 * (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹ * (s / 8)⁻¹ := by
    have : (0 : ℝ) < Real.sqrt (s / 8) := Real.sqrt_pos.mpr ht
    positivity
  exact mul_pos (mul_pos htri hD) hrest

/-- The sharp field-low window scale used in the fluctuation assembly. -/
def sharpFieldLowWindowScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ) : ℝ :=
  Ch04.gammaTriangleConst 2 * sharpFieldLowColumnScaleSum M s

theorem sharpFieldLowWindowScale_pos {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ} (hs : 0 < s) :
    0 < sharpFieldLowWindowScale M s :=
  mul_pos IndependentSums.gammaTriangleConst_pos
    (sharpFieldLowColumnScaleSum_pos M hs)

/-- The accumulated-error window fluctuation at the sharp field-low scale.  Its
`s`-power is `s ^ (-5 / 2)` in the field-low slot, against the proved
`s ^ (-4)`; every other slot is unchanged. -/
theorem isBigO_cutoffParameterizedAccumulatedErrorWindowFluctuation_sharp
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m)
      (cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
        M s A n m (sharpFieldLowWindowScale M s)) := by
  have hs8 : s / 8 ≤ 1 := by linarith
  refine isBigO_cutoffParameterizedAccumulatedErrorWindowFluctuation_gen
    M L hs hs1 z hnm hA hrow (sharpFieldLowWindowScale_pos M hs) ?_
  exact isBigO_accumulatedFiniteFieldLowWindow_sharp M z hs hs8 hnm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
