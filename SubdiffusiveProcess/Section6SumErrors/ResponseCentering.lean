import SubdiffusiveProcess.Section6SumErrors.ResponseGamma

/-!
# ResponseCentering

Centering the arbitrary-order response rows and placing them in the independent shell array.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

theorem isBigO_holderResponseRow_sub_integral (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) {A : ℝ}
    (hA : 0 < A)
    (hrow : Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      ((holderResponseRow s) M j) A) :
    Homogenization.IndependentSums.IsBigO M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      (fun omega => (holderResponseRow s) M j omega -
        ∫ eta, (holderResponseRow s) M j eta ∂M.P.toMeasure)
      ((1 + Homogenization.IndependentSums.gammaMomentConst 2) * A) := by
  obtain ⟨_hint, hmean0, hmean⟩ :=
    integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo hA
      ((measurable_holderResponseRow s) M j)
      ((holderResponseRow_nonneg s) M j) hrow
  have hcenter := isBigO_gammaTwo_sub_const_of_isBigOWith_nonneg
    hA.le hmean0 ((holderResponseRow_nonneg s) M j) hrow
  refine hcenter.mono_scale ?_
  nlinarith

/-- The response rows placed on the diagonal of a shell array. -/
noncomputable def holderResponseRowArray (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) : ℤ → ℤ → Sample d → ℝ :=
  fun k j omega ↦
    Real.sqrt (min
      (responseScoreArray M (holderResponseScoreS s) 1 1 k j omega)
      (holderResponseScoreCap s))

theorem holderResponseRowArray_nonneg (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k j : ℤ) (omega : Sample d) :
    0 ≤ (holderResponseRowArray s) M k j omega :=
  Real.sqrt_nonneg _

theorem measurable_holderResponseRowArray (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k j : ℤ) :
    Measurable ((holderResponseRowArray s) M k j) := by
  unfold holderResponseRowArray
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_responseScoreArray M (holderResponseScoreS s) 1 1 k j).min
      measurable_const)

theorem holderResponseRowArray_diag (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) :
    (holderResponseRowArray s) M (j : ℤ) (j : ℤ) = (holderResponseRow s) M j := by
  funext omega
  unfold holderResponseRowArray holderResponseRow holderResponseScore
  simp only [responseScoreArray, Int.natCast_nonneg, le_rfl, and_self, if_true,
    Int.toNat_natCast]

theorem columnsIndep_holderResponseRowArray (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      ((holderResponseRowArray s) M) (responseScoreRange d) := by
  let f : ℝ → ℝ := fun x ↦ Real.sqrt (min x (holderResponseScoreCap s))
  have hf : Measurable f := Real.continuous_sqrt.measurable.comp
    (measurable_id.min measurable_const)
  simpa only [holderResponseRowArray, f] using
    columnsIndep_comp_entry M.P.toMeasure
      (responseScoreArray M (holderResponseScoreS s) 1 1)
      (responseScoreRange d)
      (columnsIndep_responseScoreArray M (holderResponseScoreS s) 1 1) f hf

end
end SubdiffusiveProcess.Section6SumErrors.Response
