module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseWindowSplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ResidueWindow

@[expose] public section

/-!
# Residue-class concentration for parameterized cutoff response rows

The general-`s` finite-range response array is centered along its diagonal,
split into residue classes, and summed with the independent Gamma-two theorem.
This is the active-window probabilistic half of the cutoff ladder.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

noncomputable def centeredCutoffParameterizedResponseRow
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (j : ℕ) : Sample d → ℝ :=
  fun omega => cutoffParameterizedResponseRow M L s j omega -
    ∫ eta, cutoffParameterizedResponseRow M L s j eta ∂M.P.toMeasure

theorem measurable_centeredCutoffParameterizedResponseRow
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ) :
    Measurable (centeredCutoffParameterizedResponseRow M L s j) :=
  (measurable_cutoffParameterizedResponseRow M L s j).sub measurable_const

theorem isBigO_cutoffParameterizedResponseRow_sub_integral
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ)
    {A : ℝ} (hA : 0 < A)
    (hrow : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (centeredCutoffParameterizedResponseRow M L s j)
      ((1 + IndependentSums.gammaMomentConst 2) * A) := by
  obtain ⟨_hint, hmean0, hmean⟩ :=
    integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo hA
      (measurable_cutoffParameterizedResponseRow M L s j)
      (cutoffParameterizedResponseRow_nonneg M L s j) hrow
  have hcenter := isBigO_gammaTwo_sub_const_of_isBigOWith_nonneg
    hA.le hmean0 (cutoffParameterizedResponseRow_nonneg M L s j) hrow
  refine hcenter.mono_scale ?_
  nlinarith

theorem iIndepFun_centeredCutoffParameterizedResponseRow_residue
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (r b : ℕ)
    (hindep : SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (cutoffParameterizedResponseRowArray M L s) r) :
    iIndepFun
      (fun q : ℕ => centeredCutoffParameterizedResponseRow M L s (q * r + b))
      M.P.toMeasure := by
  have hdiag := (columnsIndep_diag_residue M.P.toMeasure
    (cutoffParameterizedResponseRowArray M L s) r hindep (b : ℤ)).precomp
      Int.ofNat_injective
  have hcenter := hdiag.comp
    (fun q : ℕ => fun x : ℝ => x -
      ∫ eta, cutoffParameterizedResponseRow M L s (q * r + b) eta
        ∂M.P.toMeasure)
    (fun _ => measurable_id.sub measurable_const)
  refine hcenter.congr (fun q => Filter.Eventually.of_forall fun omega => ?_)
  change cutoffParameterizedResponseRowArray M L s
      ((q : ℤ) * (r : ℤ) + (b : ℤ))
        ((q : ℤ) * (r : ℤ) + (b : ℤ)) omega -
      ∫ eta, cutoffParameterizedResponseRow M L s (q * r + b) eta
        ∂M.P.toMeasure =
    centeredCutoffParameterizedResponseRow M L s (q * r + b) omega
  rw [show (q : ℤ) * (r : ℤ) + (b : ℤ) = ((q * r + b : ℕ) : ℤ) by
    norm_num]
  rw [cutoffParameterizedResponseRowArray_diag]
  rfl

theorem integral_centeredCutoffParameterizedResponseRow_eq_zero
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ)
    {A : ℝ} (hA : 0 < A)
    (hrow : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    ∫ omega, centeredCutoffParameterizedResponseRow M L s j omega
        ∂M.P.toMeasure = 0 := by
  obtain ⟨hint, _hmean0, _hmean⟩ :=
    integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo hA
      (measurable_cutoffParameterizedResponseRow M L s j)
      (cutoffParameterizedResponseRow_nonneg M L s j) hrow
  unfold centeredCutoffParameterizedResponseRow
  rw [integral_sub hint (integrable_const _)]
  simp

noncomputable def centeredCutoffParameterizedResponseResidueSum
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (r b n m : ℕ) : Sample d → ℝ :=
  fun omega => ∑ q ∈ Finset.range (m + 1),
    if n ≤ q * r + b ∧ q * r + b ≤ m then
      centeredCutoffParameterizedResponseRow M L s (q * r + b) omega else 0

theorem measurable_centeredCutoffParameterizedResponseResidueSum
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (r b n m : ℕ) :
    Measurable (centeredCutoffParameterizedResponseResidueSum
      M L s r b n m) := by
  unfold centeredCutoffParameterizedResponseResidueSum
  apply Finset.measurable_sum
  intro q _hq
  by_cases hq : n ≤ q * r + b ∧ q * r + b ≤ m
  · simpa [hq] using!
      measurable_centeredCutoffParameterizedResponseRow
        M L s (q * r + b)
  · simpa [hq] using!
      (measurable_const : Measurable (fun _ : Sample d => (0 : ℝ)))

theorem isBigO_centeredCutoffParameterizedResponseResidueSum
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (r b n m : ℕ) (hr : 0 < r)
    (hindep : SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (cutoffParameterizedResponseRowArray M L s) r)
    {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (centeredCutoffParameterizedResponseResidueSum M L s r b n m)
      (Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
          ((1 + IndependentSums.gammaMomentConst 2) * A)) := by
  let S := (Finset.range (m + 1)).filter
    (fun q => n ≤ q * r + b ∧ q * r + b ≤ m)
  let Y : ℕ → Sample d → ℝ := fun q =>
    centeredCutoffParameterizedResponseRow M L s (q * r + b)
  let K : ℝ := (1 + IndependentSums.gammaMomentConst 2) * A
  have hK : 0 < K := by
    unfold K
    exact mul_pos (add_pos one_pos
      (IndependentSums.gammaMomentConst_pos (by norm_num))) hA
  have hC : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hYindep : iIndepFun Y M.P.toMeasure := by
    simpa only [Y] using!
      iIndepFun_centeredCutoffParameterizedResponseRow_residue
        M L s r b hindep
  have hYmeas : ∀ q, Measurable (Y q) := by
    intro q
    simpa only [Y] using!
      measurable_centeredCutoffParameterizedResponseRow M L s (q * r + b)
  have hYbig : ∀ q ∈ S,
      IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (Y q) K := by
    intro q _hq
    simpa only [Y, K] using!
      isBigO_cutoffParameterizedResponseRow_sub_integral
        M L s (q * r + b) hA (hrow (q * r + b))
  have hYmean : ∀ q ∈ S,
      ∫ omega, Y q omega ∂M.P.toMeasure = 0 := by
    intro q _hq
    simpa only [Y] using!
      integral_centeredCutoffParameterizedResponseRow_eq_zero
        M L s (q * r + b) hA (hrow (q * r + b))
  have hcard : S.card ≤ m + 1 - n := by
    rw [← Nat.card_Icc]
    apply Finset.card_le_card_of_injOn (fun q => q * r + b)
    · intro q hq
      change q ∈ (Finset.range (m + 1)).filter
        (fun q => n ≤ q * r + b ∧ q * r + b ≤ m) at hq
      rw [Finset.mem_filter] at hq
      exact Finset.mem_Icc.mpr hq.2
    · intro q _hq q' _hq' heq
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
            Real.sqrt ((m + 1 - n : ℕ) : ℝ) * K :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt hC.le) hK.le
    have hsum' := hsum.mono_scale hscale
    simpa [centeredCutoffParameterizedResponseResidueSum, S, Y, K,
      Finset.sum_filter] using! hsum'
  · have hSempt : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hcenter := isBigO_cutoffParameterizedResponseRow_sub_integral
      M L s 0 hA (hrow 0)
    have hzero := hcenter.const_mul (c := 0) (by norm_num)
    have hzero' : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (fun _ : Sample d => (0 : ℝ)) 0 := by
      simpa using! hzero
    have htarget : 0 ≤ Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) * K := by positivity
    have hzero'' := hzero'.mono_scale htarget
    have hfun : centeredCutoffParameterizedResponseResidueSum
        M L s r b n m = fun _ : Sample d => (0 : ℝ) := by
      funext omega
      unfold centeredCutoffParameterizedResponseResidueSum
      rw [← Finset.sum_filter]
      change ∑ q ∈ S,
        centeredCutoffParameterizedResponseRow M L s (q * r + b) omega = 0
      rw [hSempt]
      simp
    rw [hfun]
    simpa only [K] using! hzero''

noncomputable def centeredCutoffParameterizedResponseWindow
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (n m : ℕ) : Sample d → ℝ :=
  fun omega => ∑ j ∈ Finset.Icc n m,
    centeredCutoffParameterizedResponseRow M L s j omega

theorem centeredCutoffParameterizedResponseWindow_eq_sum_residues
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    {r n m : ℕ} (hr : 0 < r) :
    centeredCutoffParameterizedResponseWindow M L s n m = fun omega =>
      ∑ b ∈ Finset.range r,
        centeredCutoffParameterizedResponseResidueSum M L s r b n m omega := by
  funext omega
  unfold centeredCutoffParameterizedResponseWindow
    centeredCutoffParameterizedResponseResidueSum
  rw [sum_Icc_eq_sum_residue_filters
    (fun j => centeredCutoffParameterizedResponseRow M L s j omega) hr]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.sum_filter]

theorem measurable_centeredCutoffParameterizedResponseWindow
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (n m : ℕ) :
    Measurable (centeredCutoffParameterizedResponseWindow M L s n m) := by
  unfold centeredCutoffParameterizedResponseWindow
  apply Finset.measurable_sum
  intro j _hj
  exact measurable_centeredCutoffParameterizedResponseRow M L s j

theorem isBigO_centeredCutoffParameterizedResponseWindow
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (r n m : ℕ) (hr : 0 < r) (hnm : n ≤ m)
    (hindep : SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (cutoffParameterizedResponseRowArray M L s) r)
    {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (centeredCutoffParameterizedResponseWindow M L s n m)
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
      (mul_pos gammaSigmaIndependentSumConst_two_pos
        (Real.sqrt_pos.mpr (by exact_mod_cast hwindow)))
      (mul_pos (add_pos one_pos
        (IndependentSums.gammaMomentConst_pos (by norm_num))) hA)
  have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.range r)
    (X := fun b => centeredCutoffParameterizedResponseResidueSum
      M L s r b n m)
    (a := fun _ => B) (σ := 2) (by norm_num)
    (Finset.nonempty_range_iff.mpr hr.ne')
    (fun _ _ => hB)
    (fun b _ => by
      simpa only [B] using!
        isBigO_centeredCutoffParameterizedResponseResidueSum
          M L s r b n m hr hindep hA hrow)
    (fun b _ =>
      measurable_centeredCutoffParameterizedResponseResidueSum
        M L s r b n m)
  rw [centeredCutoffParameterizedResponseWindow_eq_sum_residues M L s hr]
  simpa [B, mul_assoc] using! hsum

/-- Reinsert the retained general-`s` cutoff row means after centering. -/
theorem sum_cutoffParameterizedResponseRow_le_centered_add_mean_bound
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (n m : ℕ) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    (omega : Sample d) :
    (∑ j ∈ Finset.Icc n m,
      cutoffParameterizedResponseRow M L s j omega) ≤
      centeredCutoffParameterizedResponseWindow M L s n m omega +
        ((m + 1 - n : ℕ) : ℝ) *
          (IndependentSums.gammaMomentConst 2 * A) := by
  have hmean : ∀ j : ℕ,
      ∫ eta, cutoffParameterizedResponseRow M L s j eta ∂M.P.toMeasure ≤
        IndependentSums.gammaMomentConst 2 * A := by
    intro j
    exact (integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo
      hA (measurable_cutoffParameterizedResponseRow M L s j)
      (cutoffParameterizedResponseRow_nonneg M L s j) (hrow j)).2.2
  have hcard : (Finset.Icc n m).card = m + 1 - n := by
    rw [Nat.card_Icc]
  calc
    (∑ j ∈ Finset.Icc n m,
        cutoffParameterizedResponseRow M L s j omega) =
        centeredCutoffParameterizedResponseWindow M L s n m omega +
          ∑ j ∈ Finset.Icc n m,
            ∫ eta, cutoffParameterizedResponseRow M L s j eta
              ∂M.P.toMeasure := by
      unfold centeredCutoffParameterizedResponseWindow
        centeredCutoffParameterizedResponseRow
      rw [Finset.sum_sub_distrib]
      ring
    _ ≤ centeredCutoffParameterizedResponseWindow M L s n m omega +
          ∑ _j ∈ Finset.Icc n m,
            IndependentSums.gammaMomentConst 2 * A := by
      gcongr with j hj
      exact hmean j
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

theorem cutoffParameterizedAccumulatedResponseActiveWindow_le_centered_add_mean
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (n m : ℕ)
    {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    (omega : Sample d) :
    cutoffParameterizedAccumulatedResponseActiveWindow M L s n m omega ≤
      (8 / s) *
        (centeredCutoffParameterizedResponseWindow M L s n m omega +
          ((m + 1 - n : ℕ) : ℝ) *
            (IndependentSums.gammaMomentConst 2 * A)) := by
  exact (cutoffParameterizedAccumulatedResponseActiveWindow_le_rows
    M L hs hs1 n m omega).trans
    (mul_le_mul_of_nonneg_left
      (sum_cutoffParameterizedResponseRow_le_centered_add_mean_bound
        M L s n m hA hrow omega)
      (by positivity))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
