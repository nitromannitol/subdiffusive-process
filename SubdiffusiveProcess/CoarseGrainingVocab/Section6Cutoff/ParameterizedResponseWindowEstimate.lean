module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseResidueWindow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorWindow

@[expose] public section

/-!
# Parameterized cutoff response-window estimate

The low and active general-`s` response rows are assembled into a linear mean
and one Gamma-two fluctuation.  This is the response input to the cutoff
ladder's accumulated-error average.
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

def cutoffParameterizedAccumulatedResponseWindowMeanBound
    (s A : ℝ) (n m : ℕ) : ℝ :=
  ((m + 1 - n : ℕ) : ℝ) *
    (2 * (8 / s) * (IndependentSums.gammaMomentConst 2 * A))

noncomputable def cutoffParameterizedAccumulatedResponseWindowFluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (z : Vec d) (n m : ℕ) : Sample d → ℝ :=
  fun omega => 2 * (8 / s) *
    (cutoffParameterizedAccumulatedResponseLowRows M L s n
        (translatePotentialSample z omega) +
      centeredCutoffParameterizedResponseWindow M L s n m
        (translatePotentialSample z omega))

def cutoffParameterizedAccumulatedResponseWindowFluctuationScale
    (d : ℕ) (s A : ℝ) (n m : ℕ) : ℝ :=
  2 * (8 / s) * Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * ((8 / s) * A) +
      Ch04.gammaTriangleConst 2 * (responseScoreRange d : ℝ) *
        (Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
            ((1 + IndependentSums.gammaMomentConst 2) * A)))

theorem ae_sum_translatedCutoffParameterizedAccumulatedResponseSup_le_mean_add_fluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        translatedCutoffParameterizedAccumulatedResponseSup
          M L s k z omega) ≤
        cutoffParameterizedAccumulatedResponseWindowMeanBound s A n m +
          cutoffParameterizedAccumulatedResponseWindowFluctuation
            M L s z n m omega := by
  have horigin :=
    ae_sum_cutoffParameterizedAccumulatedResponseSup_le_windowConvolution
      M L hs hs1 n m
  have htranslated :=
    (Section6Covariance.measurePreserving_translatePotentialSample M z).quasiMeasurePreserving.ae
      horigin
  filter_upwards [htranslated] with omega hwindow
  have hlow := cutoffParameterizedAccumulatedResponseLowWindow_le_decay_rows
    M L hs hs1 n m (translatePotentialSample z omega)
  have hactive :=
    cutoffParameterizedAccumulatedResponseActiveWindow_le_centered_add_mean
      M L hs hs1 n m hA hrow (translatePotentialSample z omega)
  have hsplit :=
    cutoffParameterizedAccumulatedResponseWindowConvolution_eq_low_add_active
      M L s hnm (translatePotentialSample z omega)
  calc
    (∑ k ∈ Finset.Icc n m,
        translatedCutoffParameterizedAccumulatedResponseSup
          M L s k z omega) =
        ∑ k ∈ Finset.Icc n m,
          cutoffParameterizedAccumulatedResponseSup M L s k
            (translatePotentialSample z omega) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact translatedCutoffParameterizedAccumulatedResponseSup_eq_origin_translate
        M L s k z omega
    _ ≤ 2 * cutoffParameterizedAccumulatedResponseWindowConvolution
          M L s n m (translatePotentialSample z omega) := hwindow
    _ = 2 * (cutoffParameterizedAccumulatedResponseLowWindow M L s n m
          (translatePotentialSample z omega) +
        cutoffParameterizedAccumulatedResponseActiveWindow M L s n m
          (translatePotentialSample z omega)) := by rw [hsplit]
    _ ≤ 2 * ((8 / s) *
          cutoffParameterizedAccumulatedResponseLowRows M L s n
            (translatePotentialSample z omega) +
        (8 / s) *
          (centeredCutoffParameterizedResponseWindow M L s n m
              (translatePotentialSample z omega) +
            ((m + 1 - n : ℕ) : ℝ) *
              (IndependentSums.gammaMomentConst 2 * A))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hlow hactive) (by norm_num)
    _ = cutoffParameterizedAccumulatedResponseWindowMeanBound s A n m +
          cutoffParameterizedAccumulatedResponseWindowFluctuation
            M L s z n m omega := by
      unfold cutoffParameterizedAccumulatedResponseWindowMeanBound
        cutoffParameterizedAccumulatedResponseWindowFluctuation
      ring

theorem isBigO_cutoffParameterizedAccumulatedResponseWindowFluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cutoffParameterizedAccumulatedResponseWindowFluctuation
        M L s z n m)
      (cutoffParameterizedAccumulatedResponseWindowFluctuationScale
        d s A n m) := by
  let B1 : ℝ := Ch04.gammaTriangleConst 2 * ((8 / s) * A)
  let B2 : ℝ := Ch04.gammaTriangleConst 2 * (responseScoreRange d : ℝ) *
    (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) * A))
  let c : ℝ := 2 * (8 / s)
  have hB1 : 0 < B1 := by
    unfold B1
    positivity [IndependentSums.gammaTriangleConst_pos (σ := 2)]
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
  have hc : 0 < c := by unfold c; positivity
  have hlow0 := isBigO_cutoffParameterizedAccumulatedResponseLowRows
    M L hs hs1 n hA hrow
  have hlow := isBigO_comp_translatePotentialSample M z hlow0
  have hactive0 := isBigO_centeredCutoffParameterizedResponseWindow
    M L s (responseScoreRange d) n m (responseScoreRange_pos d) hnm
    (columnsIndep_cutoffParameterizedResponseRowArray M L s) hA hrow
  have hactive := isBigO_comp_translatePotentialSample M z hactive0
  have hadd := isBigO_add_gammaTwo M hB1 hB2
    (by simpa only [B1] using! hlow)
    (by simpa only [B2] using! hactive)
    (((measurable_cutoffParameterizedAccumulatedResponseLowRows M L s n).comp
      (Section6Covariance.measurable_translatePotentialSample z)).aemeasurable)
    (((measurable_centeredCutoffParameterizedResponseWindow M L s n m).comp
      (Section6Covariance.measurable_translatePotentialSample z)).aemeasurable)
  have hscaled := hadd.const_mul hc.le
  convert hscaled using 1
  · funext omega
    simp only [cutoffParameterizedAccumulatedResponseWindowFluctuation, Function.comp_apply]
    dsimp only [c]
  · unfold cutoffParameterizedAccumulatedResponseWindowFluctuationScale
    dsimp only [B1, B2, c]
    ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
