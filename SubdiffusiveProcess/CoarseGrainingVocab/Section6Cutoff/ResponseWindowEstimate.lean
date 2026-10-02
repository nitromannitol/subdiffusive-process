import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseResidueWindow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorWindow

/-!
# Cutoff response-window estimate

This module packages the low and active finite-cutoff response rows into the
linear mean plus Gamma-two fluctuation used by the accumulated-error average.
Only the response summand changes with the cutoff; field and gradient rows are
left to the existing stopping modules.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open Filter MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

def cutoffAccumulatedResponseWindowMeanBound
    (A : ℝ) (n m : ℕ) : ℝ :=
  ((m + 1 - n : ℕ) : ℝ) *
    (2 * (8 / holderStoppingS) *
      (IndependentSums.gammaMomentConst 2 * A))

noncomputable def cutoffAccumulatedResponseWindowFluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    (n m : ℕ) : Sample d → ℝ :=
  fun omega => 2 * (8 / holderStoppingS) *
    (cutoffAccumulatedResponseLowRows M L n
        (translatePotentialSample z omega) +
      centeredCutoffHolderResponseWindow M L n m
        (translatePotentialSample z omega))

def cutoffAccumulatedResponseWindowFluctuationScale
    (d : ℕ) (A : ℝ) (n m : ℕ) : ℝ :=
  2 * (8 / holderStoppingS) * Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * ((8 / holderStoppingS) * A) +
      Ch04.gammaTriangleConst 2 * (responseScoreRange d : ℝ) *
        (Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
            ((1 + IndependentSums.gammaMomentConst 2) * A)))

theorem ae_sum_translatedCutoffAccumulatedResponseSup_le_mean_add_fluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (cutoffHolderResponseRow M L j) A) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        translatedCutoffAccumulatedResponseSup M L k z omega) ≤
        cutoffAccumulatedResponseWindowMeanBound A n m +
          cutoffAccumulatedResponseWindowFluctuation M L z n m omega := by
  have horigin :=
    ae_sum_cutoffAccumulatedResponseSup_le_windowConvolution M L n m
  have htranslated :=
    (Section6Covariance.measurePreserving_translatePotentialSample M z).quasiMeasurePreserving.ae
      horigin
  filter_upwards [htranslated] with omega hwindow
  have hlow := cutoffAccumulatedResponseLowWindow_le_decay_rows
    M L n m (translatePotentialSample z omega)
  have hactive := cutoffAccumulatedResponseActiveWindow_le_centered_add_mean
    M L n m hA hrow (translatePotentialSample z omega)
  have hlow' : cutoffAccumulatedResponseLowWindow M L n m
      (translatePotentialSample z omega) ≤
      (8 / holderStoppingS) * cutoffAccumulatedResponseLowRows M L n
        (translatePotentialSample z omega) := by
    simpa only [cutoffAccumulatedResponseLowRows] using hlow
  have hsplit := cutoffAccumulatedResponseWindowConvolution_eq_low_add_active
    M L hnm (translatePotentialSample z omega)
  calc
    (∑ k ∈ Finset.Icc n m,
        translatedCutoffAccumulatedResponseSup M L k z omega) =
        ∑ k ∈ Finset.Icc n m,
          cutoffAccumulatedResponseSup M L k
            (translatePotentialSample z omega) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact translatedCutoffAccumulatedResponseSup_eq_origin_translate
        M L k z omega
    _ ≤ 2 * cutoffAccumulatedResponseWindowConvolution M L n m
          (translatePotentialSample z omega) := hwindow
    _ = 2 * (cutoffAccumulatedResponseLowWindow M L n m
          (translatePotentialSample z omega) +
        cutoffAccumulatedResponseActiveWindow M L n m
          (translatePotentialSample z omega)) := by rw [hsplit]
    _ ≤ 2 * ((8 / holderStoppingS) *
          cutoffAccumulatedResponseLowRows M L n
            (translatePotentialSample z omega) +
        (8 / holderStoppingS) *
          (centeredCutoffHolderResponseWindow M L n m
              (translatePotentialSample z omega) +
            ((m + 1 - n : ℕ) : ℝ) *
              (IndependentSums.gammaMomentConst 2 * A))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hlow' hactive) (by norm_num)
    _ = cutoffAccumulatedResponseWindowMeanBound A n m +
          cutoffAccumulatedResponseWindowFluctuation M L z n m omega := by
      unfold cutoffAccumulatedResponseWindowMeanBound
        cutoffAccumulatedResponseWindowFluctuation
      ring

theorem isBigO_cutoffAccumulatedResponseWindowFluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (cutoffHolderResponseRow M L j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cutoffAccumulatedResponseWindowFluctuation M L z n m)
      (cutoffAccumulatedResponseWindowFluctuationScale d A n m) := by
  let B1 : ℝ := Ch04.gammaTriangleConst 2 * ((8 / holderStoppingS) * A)
  let B2 : ℝ := Ch04.gammaTriangleConst 2 * (responseScoreRange d : ℝ) *
    (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) * A))
  let c : ℝ := 2 * (8 / holderStoppingS)
  have hB1 : 0 < B1 := by
    unfold B1
    positivity [holderStoppingS_pos,
      IndependentSums.gammaTriangleConst_pos (σ := 2)]
  have hwindow : 0 < m + 1 - n := by omega
  have hB2 : 0 < B2 := by
    unfold B2
    have hr : 0 < (responseScoreRange d : ℝ) := by
      exact_mod_cast responseScoreRange_pos d
    have htri : 0 < Ch04.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos
    have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
      gammaSigmaIndependentSumConst_two_pos
    have hsqrt : 0 < Real.sqrt ((m + 1 - n : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast hwindow)
    have hmoment : 0 < 1 + IndependentSums.gammaMomentConst 2 :=
      add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
    exact mul_pos (mul_pos htri hr)
      (mul_pos (mul_pos hind hsqrt) (mul_pos hmoment hA))
  have hc : 0 < c := by unfold c; positivity [holderStoppingS_pos]
  have hlow0 := isBigO_cutoffAccumulatedResponseLowRows M L n hA hrow
  have hlow := isBigO_comp_translatePotentialSample M z hlow0
  have hactive0 := isBigO_centeredCutoffHolderResponseWindow M L
    (responseScoreRange d) n m (responseScoreRange_pos d) hnm
    (columnsIndep_cutoffHolderResponseRowArray M L) hA hrow
  have hactive := isBigO_comp_translatePotentialSample M z hactive0
  have hadd := isBigO_add_gammaTwo M hB1 hB2
    (by simpa only [B1] using hlow)
    (by simpa only [B2] using hactive)
    (((measurable_cutoffAccumulatedResponseLowRows M L n).comp
      (Section6Covariance.measurable_translatePotentialSample z)).aemeasurable)
    (((measurable_centeredCutoffHolderResponseWindow M L n m).comp
      (Section6Covariance.measurable_translatePotentialSample z)).aemeasurable)
  have hscaled := hadd.const_mul hc.le
  convert hscaled using 1
  · unfold cutoffAccumulatedResponseWindowFluctuationScale
    dsimp only [B1, B2, c]
    ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
