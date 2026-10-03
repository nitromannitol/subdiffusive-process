module

public import SubdiffusiveProcess.Section6SumErrors.MomentBridge
@[expose] public section

/-!
# WindowBounds

Almost-everywhere measurability of the window fluctuation and logarithm-absorbed bounds for the stopping argument.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal BigOperators
noncomputable section

theorem aemeasurable_fluctuation {d : ℕ} [NeZero d]
    (s : ℝ)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Homogenization.Vec d) (n m : ℕ) :
    AEMeasurable (accumulatedErrorWindowFluctuation s M z n m) M.P.toMeasure := by
  have h1 := ((measurable_accumulatedResponseLowRows s M n).comp
    (Section6Covariance.measurable_translatePotentialSample z)).aemeasurable (μ := M.P.toMeasure)
  have h2 := ((measurable_centeredHolderResponseWindow s M n m).comp
    (Section6Covariance.measurable_translatePotentialSample z)).aemeasurable (μ := M.P.toMeasure)
  have h3 := (measurable_accumulatedFiniteFieldLowWindow z s n m).aemeasurable (μ := M.P.toMeasure)
  have h4 := (measurable_centeredAccumulatedFiniteFieldActiveWindow M z s n m).aemeasurable (μ := M.P.toMeasure)
  have h5 := (measurable_centeredAccumulatedGradientWindow M z n m).aemeasurable (μ := M.P.toMeasure)
  have h6 := aemeasurable_accumulatedGradientEnvelope M m z
  exact (((h1.add h2).const_mul _).add ((h3.add h4).const_mul _)).add
    ((h5.add h6).const_mul _)

/-- The logarithm-absorbed window coefficient for the stopping argument. -/
def tailWindowCoeff (s : ℝ) (d : ℕ) (C : ℝ) : ℝ :=
  windowCoeff d C * holderLogAbsorption * s ^ (-7 / 2 : ℝ)

theorem tailWindowCoeff_pos (s : ℝ) (hs : 0 < s) (d : ℕ) (C : ℝ) :
    0 < tailWindowCoeff s d C := by
  exact mul_pos (mul_pos (windowCoeff_pos d C) holderLogAbsorption_pos)
    (Real.rpow_pos_of_pos hs _)

theorem window_bounds_log {d : ℕ}
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C : ℝ} (hC : 0 < C)
    {n m : ℕ} (hnm : n ≤ m) :
    accumulatedErrorWindowMeanBound s M
      (rowMeanCoeff s d C * M.delta) n m ≤
      ((m + 1 - n : ℕ) : ℝ) *
        (tailWindowCoeff s d C * M.delta * Real.sqrt |Real.log M.delta|) ∧
    accumulatedErrorWindowFluctuationScale s M (Real.exp 1 * holderResponseGammaScale s M C) n m ≤
      tailWindowCoeff s d C * M.delta * Real.sqrt |Real.log M.delta| *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
  have hd := M.shellPrefix.delta_pos.le
  have hK := (windowCoeff_pos d C).le
  have hU := (Real.rpow_pos_of_pos hs (-7 / 2)).le
  have hL := Real.sqrt_nonneg |Real.log M.delta|
  have hH : 1 ≤ holderLogAbsorption := by
    unfold holderLogAbsorption
    exact le_add_of_nonneg_right (by positivity)
  constructor
  · apply (meanBound_le M hs hs1 hC n m).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left (delta_le_logScale M) (mul_nonneg hK hU)
    convert h using 1 <;> unfold tailWindowCoeff <;> ring
  · apply (fluctuationScale_le M hs hs1 hC hnm).trans
    have h := le_mul_of_one_le_right
      (show 0 ≤ windowCoeff d C * s ^ (-7 / 2 : ℝ) * M.delta *
        Real.sqrt |Real.log M.delta| * Real.sqrt ((m + 1 - n : ℕ) : ℝ) by positivity) hH
    convert h using 1 <;> unfold tailWindowCoeff <;> ring

end
end SubdiffusiveProcess.Section6SumErrors.Response
