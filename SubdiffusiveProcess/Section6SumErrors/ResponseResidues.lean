import SubdiffusiveProcess.Section6SumErrors.ResponseCentering
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ResidueWindow

/-!
# ResponseResidues

Gaussian sums of response rows in residue classes of the finite shell-dependence range.
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

/-- The response row with its expectation subtracted. -/
noncomputable def centeredHolderResponseRow (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) : Sample d → ℝ :=
  fun omega ↦ (holderResponseRow s) M j omega -
    ∫ eta, (holderResponseRow s) M j eta ∂M.P.toMeasure

theorem measurable_centeredHolderResponseRow (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) :
    Measurable ((centeredHolderResponseRow s) M j) := by
  exact ((measurable_holderResponseRow s) M j).sub measurable_const

theorem iIndepFun_centeredHolderResponseRow_residue (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (r b : ℕ)
    (hindep : SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      ((holderResponseRowArray s) M) r) :
    iIndepFun (fun q : ℕ ↦ (centeredHolderResponseRow s) M (q * r + b))
      M.P.toMeasure := by
  have hdiag := (columnsIndep_diag_residue M.P.toMeasure
    ((holderResponseRowArray s) M) r hindep (b : ℤ)).precomp
      Int.ofNat_injective
  have hcenter := hdiag.comp
    (fun q : ℕ ↦ fun x : ℝ ↦ x -
      ∫ eta, (holderResponseRow s) M (q * r + b) eta ∂M.P.toMeasure)
    (fun _ ↦ measurable_id.sub measurable_const)
  refine hcenter.congr (fun q ↦ Filter.Eventually.of_forall fun omega ↦ ?_)
  change (holderResponseRowArray s) M
      ((q : ℤ) * (r : ℤ) + (b : ℤ))
        ((q : ℤ) * (r : ℤ) + (b : ℤ)) omega -
      ∫ eta, (holderResponseRow s) M (q * r + b) eta ∂M.P.toMeasure =
    (centeredHolderResponseRow s) M (q * r + b) omega
  rw [show (q : ℤ) * (r : ℤ) + (b : ℤ) = ((q * r + b : ℕ) : ℤ) by
    norm_num]
  rw [(holderResponseRowArray_diag s)]
  rfl

theorem iIndepFun_centeredHolderResponseRow_residue_masked (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (r b n m : ℕ)
    (hindep : SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      ((holderResponseRowArray s) M) r) :
    iIndepFun (fun q : ℕ ↦ fun omega ↦
      if n ≤ q * r + b ∧ q * r + b ≤ m then
        (centeredHolderResponseRow s) M (q * r + b) omega else 0)
      M.P.toMeasure := by
  have hbase := (iIndepFun_centeredHolderResponseRow_residue s) M r b hindep
  have hmask := hbase.comp
    (fun q : ℕ ↦ fun x : ℝ ↦
      if n ≤ q * r + b ∧ q * r + b ≤ m then x else 0)
    (fun q ↦ by
      by_cases hq : n ≤ q * r + b ∧ q * r + b ≤ m
      · simpa only [hq, if_true] using (measurable_id : Measurable (fun x : ℝ ↦ x))
      · simpa only [hq, if_false] using (measurable_const : Measurable (fun _ : ℝ ↦ (0 : ℝ))))
  simpa only [Function.comp_apply] using hmask

theorem integral_centeredHolderResponseRow_eq_zero (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) {A : ℝ}
    (hA : 0 < A)
    (hrow : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) ((holderResponseRow s) M j) A) :
    ∫ omega, (centeredHolderResponseRow s) M j omega ∂M.P.toMeasure = 0 := by
  obtain ⟨hint, _hmean0, _hmean⟩ :=
    integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo hA
      ((measurable_holderResponseRow s) M j) ((holderResponseRow_nonneg s) M j) hrow
  unfold centeredHolderResponseRow
  rw [integral_sub hint (integrable_const _)]
  simp

/-- The centered response sum in one residue class of scales. -/
noncomputable def centeredHolderResponseResidueSum (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (r b n m : ℕ) :
    Sample d → ℝ :=
  fun omega ↦ ∑ q ∈ Finset.range (m + 1),
    if n ≤ q * r + b ∧ q * r + b ≤ m then
      (centeredHolderResponseRow s) M (q * r + b) omega else 0

theorem measurable_centeredHolderResponseResidueSum (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (r b n m : ℕ) :
    Measurable ((centeredHolderResponseResidueSum s) M r b n m) := by
  unfold centeredHolderResponseResidueSum
  apply Finset.measurable_sum
  intro q _hq
  by_cases hq : n ≤ q * r + b ∧ q * r + b ≤ m
  · simpa only [hq, if_true] using
      (measurable_centeredHolderResponseRow s) M (q * r + b)
  · simpa only [hq, if_false] using
      (measurable_const : Measurable (fun _ : Sample d ↦ (0 : ℝ)))

theorem isBigO_centeredHolderResponseResidueSum (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (r b n m : ℕ)
    (hr : 0 < r)
    (hindep : SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      ((holderResponseRowArray s) M) r)
    {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) ((holderResponseRow s) M j) A) :
    IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      ((centeredHolderResponseResidueSum s) M r b n m)
      (Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
          ((1 + IndependentSums.gammaMomentConst 2) * A)) := by
  let S := (Finset.range (m + 1)).filter
    (fun q ↦ n ≤ q * r + b ∧ q * r + b ≤ m)
  let Y : ℕ → Sample d → ℝ := fun q ↦
    (centeredHolderResponseRow s) M (q * r + b)
  let K : ℝ := (1 + IndependentSums.gammaMomentConst 2) * A
  have hK : 0 < K := by
    unfold K
    exact mul_pos (add_pos one_pos
      (IndependentSums.gammaMomentConst_pos (by norm_num))) hA
  have hC : 0 < Ch04.gammaSigmaIndependentSumConst 2 := by
    have hcore : 0 < IndependentSums.gammaSigmaExpRegimeConst 2 := by
      unfold IndependentSums.gammaSigmaExpRegimeConst
      exact (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
        (IndependentSums.gammaMomentConst_pos (by norm_num))).trans_le
          (le_max_left _ _)
    rw [Ch04.gammaSigmaIndependentSumConst, if_neg (by norm_num),
      Ch04.gammaSigmaExpRegimeEndpointConst,
      IndependentSums.gammaSigmaExpRegimeEndpointConst, if_neg (by norm_num)]
    exact mul_pos (by norm_num) hcore
  have hYindep : iIndepFun Y M.P.toMeasure := by
    simpa only [Y] using
      (iIndepFun_centeredHolderResponseRow_residue s) M r b hindep
  have hYmeas : ∀ q, Measurable (Y q) := by
    intro q
    simpa only [Y] using (measurable_centeredHolderResponseRow s) M (q * r + b)
  have hYbig : ∀ q ∈ S,
      IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (Y q) K := by
    intro q _hq
    simpa only [Y, K] using
      (isBigO_holderResponseRow_sub_integral s) M (q * r + b) hA
        (hrow (q * r + b))
  have hYmean : ∀ q ∈ S,
      ∫ omega, Y q omega ∂M.P.toMeasure = 0 := by
    intro q _hq
    simpa only [Y] using
      (integral_centeredHolderResponseRow_eq_zero s) M (q * r + b) hA
        (hrow (q * r + b))
  have hcard : S.card ≤ m + 1 - n := by
    rw [← Nat.card_Icc]
    apply Finset.card_le_card_of_injOn (fun q ↦ q * r + b)
    · intro q hq
      change q ∈ (Finset.range (m + 1)).filter
        (fun q ↦ n ≤ q * r + b ∧ q * r + b ≤ m) at hq
      rw [Finset.mem_filter] at hq
      exact Finset.mem_Icc.mpr hq.2
    · intro q hq q' hq' heq
      apply Nat.mul_right_cancel hr
      exact Nat.add_right_cancel heq
  by_cases hS : S.Nonempty
  · have hsum :=
      Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := M.P.toMeasure) (X := Y) (s := S)
        (σ := 2) (K := K) hYindep hYmeas hS (by norm_num) (by norm_num)
        hK hYbig hYmean
    have hsqrt : Real.sqrt (S.card : ℝ) ≤
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hcard
    have hscale :
        Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (S.card : ℝ) * K ≤
          Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ) * K := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt
          hC.le) hK.le
    have hsum' := hsum.mono_scale hscale
    simpa [centeredHolderResponseResidueSum, S, Y, K,
      Finset.sum_filter] using hsum'
  · have hSempt : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hcenter := (isBigO_holderResponseRow_sub_integral s) M 0 hA (hrow 0)
    have hzero := hcenter.const_mul (c := 0) (by norm_num)
    have hzero' : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (fun _ : Sample d ↦ (0 : ℝ)) 0 := by
      simpa using hzero
    have htarget : 0 ≤ Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) * K := by positivity
    have hzero'' := hzero'.mono_scale htarget
    have hfun : (centeredHolderResponseResidueSum s) M r b n m =
        fun _ : Sample d ↦ (0 : ℝ) := by
      funext omega
      unfold centeredHolderResponseResidueSum
      rw [← Finset.sum_filter]
      change ∑ q ∈ S, (centeredHolderResponseRow s) M (q * r + b) omega = 0
      rw [hSempt]
      simp
    rw [hfun]
    simpa only [K] using hzero''

/-- The centered response sum over the closed scale window. -/
noncomputable def centeredHolderResponseWindow (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ) : Sample d → ℝ :=
  fun omega ↦ ∑ j ∈ Finset.Icc n m, (centeredHolderResponseRow s) M j omega

theorem centeredHolderResponseWindow_eq_sum_residues (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {r n m : ℕ} (hr : 0 < r) :
    (centeredHolderResponseWindow s) M n m = fun omega ↦
      ∑ b ∈ Finset.range r, (centeredHolderResponseResidueSum s) M r b n m omega := by
  funext omega
  unfold centeredHolderResponseWindow centeredHolderResponseResidueSum
  rw [sum_Icc_eq_sum_residue_filters
    (fun j ↦ (centeredHolderResponseRow s) M j omega) hr]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_filter]

theorem measurable_centeredHolderResponseWindow (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ) :
    Measurable ((centeredHolderResponseWindow s) M n m) := by
  unfold centeredHolderResponseWindow
  apply Finset.measurable_sum
  intro j _hj
  exact (measurable_centeredHolderResponseRow s) M j

theorem gammaSigmaIndependentSumConst_two_pos :
    0 < Ch04.gammaSigmaIndependentSumConst 2 := by
  have hcore : 0 < IndependentSums.gammaSigmaExpRegimeConst 2 := by
    unfold IndependentSums.gammaSigmaExpRegimeConst
    exact (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
      (IndependentSums.gammaMomentConst_pos (by norm_num))).trans_le
        (le_max_left _ _)
  rw [Ch04.gammaSigmaIndependentSumConst, if_neg (by norm_num),
    Ch04.gammaSigmaExpRegimeEndpointConst,
    IndependentSums.gammaSigmaExpRegimeEndpointConst, if_neg (by norm_num)]
  exact mul_pos (by norm_num) hcore

theorem isBigO_centeredHolderResponseWindow (s : ℝ)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (r n m : ℕ) (hr : 0 < r)
    (hnm : n ≤ m)
    (hindep : SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      ((holderResponseRowArray s) M) r)
    {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) ((holderResponseRow s) M j) A) :
    IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      ((centeredHolderResponseWindow s) M n m)
      (Ch04.gammaTriangleConst 2 * (r : ℝ) *
        (Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
            ((1 + IndependentSums.gammaMomentConst 2) * A))) := by
  let B : ℝ := Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) * A)
  have hB : 0 < B := by
    unfold B
    have hwindow : 0 < m + 1 - n := by omega
    exact mul_pos
      (mul_pos (gammaSigmaIndependentSumConst_two_pos)
        (Real.sqrt_pos.mpr (by exact_mod_cast hwindow)))
      (mul_pos (add_pos one_pos
        (IndependentSums.gammaMomentConst_pos (by norm_num))) hA)
  have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.range r)
    (X := fun b ↦ (centeredHolderResponseResidueSum s) M r b n m)
    (a := fun _ ↦ B) (σ := 2) (by norm_num)
    (Finset.nonempty_range_iff.mpr hr.ne')
    (fun _ _ ↦ hB)
    (fun b _ ↦ by
      simpa only [B] using (isBigO_centeredHolderResponseResidueSum s)
        M r b n m hr hindep hA hrow)
    (fun b _ ↦ (measurable_centeredHolderResponseResidueSum s) M r b n m)
  rw [(centeredHolderResponseWindow_eq_sum_residues s) M hr]
  simpa [B, mul_assoc] using hsum

end
end SubdiffusiveProcess.Section6SumErrors.Response
