module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpErrorWindowFluctuation
public import SubdiffusiveProcess.Assumptions.OGammaBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.LiteralSupMeasurability

@[expose] public section




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

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The gradient envelope is measurable, not merely a.e. measurable. -/
theorem measurable_accumulatedGradientEnvelope {d : ℕ} (k : ℕ) (z : Vec d) :
    Measurable (accumulatedGradientEnvelope (d := d) k z) := by
  unfold accumulatedGradientEnvelope
  exact measurable_const.mul
    (measurable_tsum_of_nonneg (fun q ↦ measurable_accumulatedGradientLayer k q z)
      (fun q omega ↦ accumulatedGradientLayer_nonneg k q z omega))

/-- The accumulated-error window fluctuation carrier is measurable. -/
theorem measurable_cutoffParameterizedAccumulatedErrorWindowFluctuation
    {d : ℕ} [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ)
    (z : Vec d) (n m : ℕ) :
    Measurable
      (cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m) := by
  unfold cutoffParameterizedAccumulatedErrorWindowFluctuation
    cutoffParameterizedAccumulatedResponseWindowFluctuation
  refine (((((measurable_cutoffParameterizedAccumulatedResponseLowRows
      M L s n).comp
        (Section6Covariance.measurable_translatePotentialSample z)).add
    ((measurable_centeredCutoffParameterizedResponseWindow M L s n m).comp
      (Section6Covariance.measurable_translatePotentialSample z))).const_mul
        _).add ?_).add ?_
  · exact measurable_const.mul
      ((measurable_accumulatedFiniteFieldLowWindow z s n m).add
        (measurable_centeredAccumulatedFiniteFieldActiveWindow M z s n m))
  · exact measurable_const.mul
      ((measurable_centeredAccumulatedGradientWindow M z n m).add
        (measurable_accumulatedGradientEnvelope m z))

/-- **Expectation form of the sharp window fluctuation bound.**  This is the
whole probabilistic content of conjunct (2); the separate step is the
transfer to the `accumulatedError` observable the statement names, which
is a measurability question and not an estimate (see the module docstring). -/
theorem ogammaLE_cutoffParameterizedAccumulatedErrorWindowFluctuation_sharp
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    (hpos : 0 < cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
      M s A n m (sharpFieldLowWindowScale M s)) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2
      ((4 : ℝ) ^ (2 : ℝ)⁻¹ *
        cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
          (sharpFieldLowWindowScale M s))
      (cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m) := by
  have : IsProbabilityMeasure M.P.toMeasure := M.P.prop
  exact SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma (by norm_num) hpos
    (measurable_cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m)
    (isBigO_cutoffParameterizedAccumulatedErrorWindowFluctuation_sharp
      M L hs hs1 z hnm hA hrow)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
