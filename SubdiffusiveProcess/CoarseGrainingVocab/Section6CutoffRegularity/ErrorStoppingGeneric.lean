module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ErrorStoppingAnalytic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ErrorWindowGeneric
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ErrorStoppingDepthTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ErrorStoppingAnalytic

@[expose] public section

/-!
# Arbitrary-`s` finite-cutoff accumulated-error stopping tail

The `s`-generic re-derivation of
`Section6Cutoff/ErrorStoppingAnalytic.lean`, which is pinned to
`holderStoppingS`.  The union-bound plumbing
(`cutoffAccumulatedErrorSpatialFailure`,
`cutoffErrorStoppingDepth_tail_subset_iUnion`, `cutoffErrorStoppingDepth`)
is already generic in `s`, so only the analytic chain is rebuilt here, on top
of the one-centre step of `ErrorWindowGeneric.lean`.

Two deliberate deviations from the fixed-scale original:

* every exponent is **unshifted** — `q` rather than `(q-1)_+`; and
* the window coefficient is carried abstractly as `Aw`, so the chain is
  independent of how the window bounds are eventually proved.

The response-row Gamma-two hypothesis is genuinely discharged at the end
through `exists_isBigOWith_gammaTwo_cutoffParameterizedResponseRow_of_budget`,
whose side condition `K δ² |log δ| ≤ s` is exactly the frozen conjunct's own.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open Homogenization hiding Vec
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The spatial coefficient: the window coefficient inflated by the
grid-centre entropy of dimension `d`. -/
noncomputable def errorSpatialScale (d : ℕ) (Aw : ℝ) : ℝ :=
  4 * holderErrorSpatialEntropy d * Aw

theorem errorSpatialScale_pos (d : ℕ) {Aw : ℝ} (hAw : 0 < Aw) :
    0 < errorSpatialScale d Aw :=
  mul_pos (mul_pos (by norm_num)
    (zero_lt_one.trans_le (holderErrorSpatialEntropy_one_le d))) hAw

/-- The stopping depth never exceeds `m + 1`.  Proved here rather than
imported, so this module does not depend on the fixed-scale analytic file. -/
theorem cutoffErrorStoppingDepth_le_succ_generic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (lambda s : ℝ)
    (m : ℕ) (omega : Sample d) :
    cutoffErrorStoppingDepth M L lambda s m omega ≤ m + 1 := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffErrorStoppingDepth_le_succ (d := d) (M := M) (L := L) (lambda := lambda) (s := s) (m := m) (omega := omega)

/-- Arbitrary-`s` one-centre tail at the physical threshold `lambda (m-n)`. -/
theorem measureReal_cutoffParameterizedAccumulatedError_oneCenter_le_exp_rate
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {A Aw lambda : ℝ} (hA : 0 < A) (hAw : 0 < Aw) {n m : ℕ} (hnm : n < m)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    (hmean : cutoffParameterizedAccumulatedErrorWindowMeanBound M s A n m ≤
      ((m + 1 - n : ℕ) : ℝ) * Aw)
    (hfluct :
      cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
        (sharpFieldLowWindowScale M s) ≤
        Aw * Real.sqrt ((m + 1 - n : ℕ) : ℝ))
    (hlambda : 4 * Aw ≤ lambda) :
    M.P.toMeasure.real {omega | lambda * ((m : ℝ) - (n : ℝ)) <
        ∑ k ∈ Finset.Icc n m,
          accumulatedError M (some L) k z s omega} ≤
      Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) / (4 * Aw)) ^
        (2 : ℝ))) := by
  set W : ℝ := ((m + 1 - n : ℕ) : ℝ) with hWdef
  set gap : ℝ := (m : ℝ) - (n : ℝ) with hgapdef
  set t : ℝ := lambda * Real.sqrt W / (4 * Aw) with htdef
  have hgap : 0 < gap := by
    rw [hgapdef]
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hW : W = gap + 1 := by
    rw [hWdef, hgapdef, show m + 1 - n = (m - n) + 1 by omega,
      Nat.cast_add, Nat.cast_one, Nat.cast_sub hnm.le]
  have hgapOne : 1 ≤ gap := by
    rw [hgapdef]
    have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hnm)
    linarith
  have hWpos : 0 < W := by rw [hW]; linarith
  have hWle : W ≤ 2 * gap := by rw [hW]; linarith
  have hsqrtW : 1 ≤ Real.sqrt W := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by rw [hW]; linarith)
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by linarith) hlambda
  have ht : 1 ≤ t := by
    rw [htdef, le_div_iff₀ (by linarith : (0:ℝ) < 4 * Aw), one_mul]
    calc 4 * Aw ≤ lambda := hlambda
      _ ≤ lambda * Real.sqrt W := le_mul_of_one_le_right hlambdaPos.le hsqrtW
  have hmeanThreshold :
      cutoffParameterizedAccumulatedErrorWindowMeanBound M s A n m ≤
        lambda * gap / 2 := by
    calc _ ≤ W * Aw := hmean
      _ ≤ (2 * gap) * Aw := mul_le_mul_of_nonneg_right hWle hAw.le
      _ ≤ lambda * gap / 2 := by nlinarith [mul_le_mul_of_nonneg_right hlambda hgap.le]
  have hsqrtSq : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hWpos.le
  have hfluctThreshold :
      cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
        (sharpFieldLowWindowScale M s) * t ≤
        lambda * gap / 2 := by
    calc _ ≤ (Aw * Real.sqrt W) * t :=
          mul_le_mul_of_nonneg_right hfluct (zero_le_one.trans ht)
      _ = lambda * W / 4 := by
          rw [htdef]
          field_simp
          nlinarith [hsqrtSq]
      _ ≤ lambda * gap / 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hWle hlambdaPos.le]
  refine measureReal_cutoffParameterizedAccumulatedError_oneCenter_le_exp
    M L hs hs1 z hnm.le hA hrow ht ?_
  linarith

/-- Spatial union over the exact cutoff grid centres, arbitrary `s`. -/
theorem measureReal_cutoffParameterizedSpatialFailure_le_card_mul_exp
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1)
    {A Aw lambda : ℝ} (hA : 0 < A) (hAw : 0 < Aw) {n m : ℕ} (hnm : n < m)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    (hmean : cutoffParameterizedAccumulatedErrorWindowMeanBound M s A n m ≤
      ((m + 1 - n : ℕ) : ℝ) * Aw)
    (hfluct :
      cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
        (sharpFieldLowWindowScale M s) ≤
        Aw * Real.sqrt ((m + 1 - n : ℕ) : ℝ))
    (hlambda : 4 * Aw ≤ lambda) :
    M.P.toMeasure.real
        (cutoffAccumulatedErrorSpatialFailure M L lambda s n m) ≤
      (3 ^ (d * (m - n)) : ℕ) *
        Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) / (4 * Aw)) ^
          (2 : ℝ))) := by
  set centers := gridCentersInCube d n m with hcdef
  set E : Vec d → Set (Sample d) := fun z =>
    {omega | lambda * ((m : ℝ) - (n : ℝ)) <
      ∑ k ∈ Finset.Icc n m, accumulatedError M (some L) k z s omega} with hEdef
  have hevent :
      cutoffAccumulatedErrorSpatialFailure M L lambda s n m =
        ⋃ z ∈ centers, E z := by
    ext omega
    constructor
    · rintro ⟨z, hzgrid, hzmem, hzfail⟩
      exact Set.mem_iUnion₂.2 ⟨z,
        (mem_gridCentersInCube_iff hnm.le).2 ⟨hzgrid, hzmem⟩, hzfail⟩
    · rintro homega
      obtain ⟨z, hzmem, hzfail⟩ := Set.mem_iUnion₂.1 homega
      obtain ⟨hzgrid, hzcube⟩ := (mem_gridCentersInCube_iff hnm.le).1 hzmem
      exact ⟨z, hzgrid, hzcube, hzfail⟩
  rw [hevent]
  calc
    M.P.toMeasure.real (⋃ z ∈ centers, E z) ≤
        ∑ z ∈ centers, M.P.toMeasure.real (E z) :=
      measureReal_biUnion_finset_le centers E
    _ ≤ ∑ _z ∈ centers,
        Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) / (4 * Aw)) ^
          (2 : ℝ))) := by
      refine Finset.sum_le_sum fun z _hz => ?_
      exact measureReal_cutoffParameterizedAccumulatedError_oneCenter_le_exp_rate
        M L hs hs1 z hA hAw hnm hrow hmean hfluct hlambda
    _ = (3 ^ (d * (m - n)) : ℕ) *
        Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) / (4 * Aw)) ^
          (2 : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcdef, card_gridCentersInCube hnm.le]

/-- The grid-centre entropy absorbed into the Gaussian exponent. -/
theorem measureReal_cutoffParameterizedSpatialFailure_le_exp
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1)
    {A Aw lambda u : ℝ} (hA : 0 < A) (hAw : 0 < Aw) (hu : 1 ≤ u)
    {n m : ℕ} (hnm : n < m)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    (hmean : cutoffParameterizedAccumulatedErrorWindowMeanBound M s A n m ≤
      ((m + 1 - n : ℕ) : ℝ) * Aw)
    (hfluct :
      cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
        (sharpFieldLowWindowScale M s) ≤
        Aw * Real.sqrt ((m + 1 - n : ℕ) : ℝ))
    (hlambda : errorSpatialScale d Aw * u ≤ lambda) :
    M.P.toMeasure.real
        (cutoffAccumulatedErrorSpatialFailure M L lambda s n m) ≤
      Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ)))) := by
  set Q : ℝ := holderErrorSpatialEntropy d with hQdef
  set W : ℝ := ((m + 1 - n : ℕ) : ℝ) with hWdef
  set gap : ℝ := (m : ℝ) - (n : ℝ) with hgapdef
  set t : ℝ := lambda * Real.sqrt W / (4 * Aw) with htdef
  have hQ : 1 ≤ Q := holderErrorSpatialEntropy_one_le d
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hgap : 0 < gap := by
    rw [hgapdef]
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hWgap : gap ≤ W := by
    rw [hgapdef, hWdef, show m + 1 - n = (m - n) + 1 by omega,
      Nat.cast_add, Nat.cast_one, Nat.cast_sub hnm.le]
    linarith
  have hW0 : 0 ≤ W := hgap.le.trans hWgap
  have hsqrtW0 : 0 ≤ Real.sqrt W := Real.sqrt_nonneg _
  have hSeq : errorSpatialScale d Aw = 4 * Q * Aw := by
    rw [errorSpatialScale, hQdef]
  have hgiven : 4 * Q * Aw * u ≤ lambda := by
    rw [← hSeq]
    exact hlambda
  have hlambda' : 4 * Aw ≤ lambda := by
    have h1 : 4 * Aw * 1 ≤ 4 * Aw * Q :=
      mul_le_mul_of_nonneg_left hQ (by linarith)
    have h2 : 4 * Aw * Q ≤ 4 * Aw * Q * u :=
      le_mul_of_one_le_right (by positivity) hu
    have h3 : 4 * Aw * Q * u = 4 * Q * Aw * u := by ring
    linarith [h3 ▸ h2]
  have htLower : Q * u * Real.sqrt W ≤ t := by
    rw [htdef, le_div_iff₀ (by linarith : (0:ℝ) < 4 * Aw)]
    have hmul := mul_le_mul_of_nonneg_right
      (show 4 * Aw * (Q * u) ≤ lambda by linarith [hgiven]) hsqrtW0
    calc Q * u * Real.sqrt W * (4 * Aw)
        = 4 * Aw * (Q * u) * Real.sqrt W := by ring
      _ ≤ lambda * Real.sqrt W := hmul
  have ht0 : 0 ≤ t :=
    (mul_nonneg (mul_nonneg hQ0 hu0) hsqrtW0).trans htLower
  have hQsq : Q ^ 2 = 2 * (d : ℝ) * Real.log 3 + 1 := by
    rw [hQdef, holderErrorSpatialEntropy]
    refine Real.sq_sqrt ?_
    have hlog : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
    positivity
  have hWsq : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hW0
  have htSq : (Q * u * Real.sqrt W) ^ 2 ≤ t ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (mul_nonneg hQ0 hu0) hsqrtW0) ht0).2 htLower
  have hrate : (d : ℝ) * Real.log 3 * gap - t ^ 2 ≤ -(u ^ 2 * gap) := by
    have hdlog : 0 ≤ (d : ℝ) * Real.log 3 := by
      have hlog : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
      positivity
    have huSq : 1 ≤ u ^ 2 := by nlinarith
    rw [mul_pow, mul_pow, hQsq, hWsq] at htSq
    have hgapW := mul_le_mul_of_nonneg_left hWgap
      (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (d : ℝ) * Real.log 3 + 1)
        (sq_nonneg u))
    nlinarith [mul_nonneg hdlog (sub_nonneg.mpr huSq)]
  have hcardExp : (((3 ^ (d * (m - n)) : ℕ) : ℝ)) =
      Real.exp ((d : ℝ) * Real.log 3 * gap) := by
    have hexponent : (((d * (m - n) : ℕ) : ℝ) * Real.log 3) =
        (d : ℝ) * Real.log 3 * gap := by
      rw [hgapdef, Nat.cast_mul, Nat.cast_sub hnm.le]
      ring
    rw [← hexponent, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have hraw := measureReal_cutoffParameterizedSpatialFailure_le_card_mul_exp
    M L hs hs1 hA hAw hnm hrow hmean hfluct hlambda'
  calc
    M.P.toMeasure.real
        (cutoffAccumulatedErrorSpatialFailure M L lambda s n m) ≤
      ((3 ^ (d * (m - n)) : ℕ) : ℝ) * Real.exp (-(t ^ (2 : ℝ))) := hraw
    _ = Real.exp ((d : ℝ) * Real.log 3 * gap - t ^ 2) := by
      rw [hcardExp, ← Real.exp_add]
      congr 1
      rw [show t ^ (2 : ℝ) = t ^ 2 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
      ring
    _ ≤ Real.exp (-(u ^ 2 * gap)) := Real.exp_le_exp.mpr hrate

/-- The arbitrary-`s` depth tail, in the unshifted `q` convention. -/
theorem measureReal_cutoffParameterizedErrorStoppingDepth_tail_le_two_exp
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1)
    {A Aw lambda u : ℝ} (hA : 0 < A) (hAw : 0 < Aw) (hu : 1 ≤ u)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    (hwin : ∀ n m : ℕ, n ≤ m →
      cutoffParameterizedAccumulatedErrorWindowMeanBound M s A n m ≤
        ((m + 1 - n : ℕ) : ℝ) * Aw ∧
      cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
        (sharpFieldLowWindowScale M s) ≤
        Aw * Real.sqrt ((m + 1 - n : ℕ) : ℝ))
    (hlambda : errorSpatialScale d Aw * u ≤ lambda)
    (q m : ℕ) (hq : 0 < q) :
    M.P.toMeasure.real {omega |
        q < cutoffErrorStoppingDepth M L lambda s m omega} ≤
      2 * Real.exp (-(u ^ 2 * (q : ℝ))) := by
  by_cases hqm : q ≤ m
  · have hsubset :=
      cutoffErrorStoppingDepth_tail_subset_iUnion M L lambda s q m hq
    have hchain :
        M.P.toMeasure.real {omega |
            q < cutoffErrorStoppingDepth M L lambda s m omega} ≤
          ∑ n ∈ Finset.range (m - q + 1),
            Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ)))) := by
      calc
        M.P.toMeasure.real {omega |
            q < cutoffErrorStoppingDepth M L lambda s m omega} ≤
          M.P.toMeasure.real (⋃ n ∈ Finset.range (m - q + 1),
            cutoffAccumulatedErrorSpatialFailure M L lambda s n m) :=
          ENNReal.toReal_mono (measure_ne_top _ _)
            (MeasureTheory.measure_mono hsubset)
        _ ≤ ∑ n ∈ Finset.range (m - q + 1),
            M.P.toMeasure.real
              (cutoffAccumulatedErrorSpatialFailure M L lambda s n m) :=
          measureReal_biUnion_finset_le _ _
        _ ≤ ∑ n ∈ Finset.range (m - q + 1),
            Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ)))) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hnlt : n < m := by
            rw [Finset.mem_range] at hn
            omega
          obtain ⟨hmean, hfluct⟩ := hwin n m hnlt.le
          exact measureReal_cutoffParameterizedSpatialFailure_le_exp
            M L hs hs1 hA hAw hu hnlt hrow hmean hfluct hlambda
    exact hchain.trans (sum_exp_neg_sq_gap_le hu hqm)
  · have hevent : {omega : Sample d |
        q < cutoffErrorStoppingDepth M L lambda s m omega} = ∅ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt_of_ge
        ((cutoffErrorStoppingDepth_le_succ_generic M L lambda s m omega).trans
          (by omega : m + 1 ≤ q))
    rw [hevent]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    positivity

/-- The arbitrary-`s` depth tail at the physical threshold. -/
theorem measureReal_cutoffParameterizedErrorStoppingDepth_tail_le_ratio
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1)
    {A Aw lambda : ℝ} (hA : 0 < A) (hAw : 0 < Aw)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    (hwin : ∀ n m : ℕ, n ≤ m →
      cutoffParameterizedAccumulatedErrorWindowMeanBound M s A n m ≤
        ((m + 1 - n : ℕ) : ℝ) * Aw ∧
      cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
        (sharpFieldLowWindowScale M s) ≤
        Aw * Real.sqrt ((m + 1 - n : ℕ) : ℝ))
    (hlambda : errorSpatialScale d Aw ≤ lambda)
    (q m : ℕ) (hq : 0 < q) :
    M.P.toMeasure.real {omega |
        q < cutoffErrorStoppingDepth M L lambda s m omega} ≤
      2 * Real.exp (-(lambda ^ 2 / errorSpatialScale d Aw ^ 2 * (q : ℝ))) := by
  set S : ℝ := errorSpatialScale d Aw with hSdef
  have hS : 0 < S := errorSpatialScale_pos d hAw
  set u : ℝ := lambda / S with hudef
  have hu : 1 ≤ u := by
    rw [hudef, le_div_iff₀ hS, one_mul]
    exact hlambda
  have hscaled : S * u ≤ lambda := by
    have heq : S * u = lambda := by
      rw [hudef]
      field_simp
    rw [heq]
  have htail := measureReal_cutoffParameterizedErrorStoppingDepth_tail_le_two_exp
    M L hs hs1 hA hAw hu hrow hwin hscaled q m hq
  refine htail.trans (le_of_eq ?_)
  congr 2
  rw [hudef, div_pow]

/-- **The arbitrary-`s` finite-cutoff error stopping tail.**  The
response-row hypothesis is discharged; the only remaining input is the
window-scale bound `CutoffParameterizedErrorWindowInput`. -/
theorem exists_cutoffParameterizedErrorStoppingDepth_tail
    {d : ℕ} [NeZero d] (hwin : CutoffParameterizedErrorWindowInput d) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ), 0 < s → s ≤ 1 →
        K * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ lambda : ℝ,
          C * s ^ (-7 / 2 : ℝ) * M.delta *
              Real.sqrt |Real.log M.delta| ≤ lambda →
          ∀ L q m : ℕ, 0 < q →
            M.P.toMeasure.real {omega |
                q < cutoffErrorStoppingDepth M L lambda s m omega} ≤
              2 * Real.exp (-(lambda ^ 2 /
                (C * s ^ (-7 / 2 : ℝ) * M.delta *
                  Real.sqrt |Real.log M.delta|) ^ 2 * (q : ℝ))) := by
  obtain ⟨Krow, Crow, hKrow, hCrow, hrow⟩ :=
    exists_isBigOWith_gammaTwo_cutoffParameterizedResponseRow_of_budget (d := d)
  obtain ⟨Kw, Cw, hKw, hCw, hbounds⟩ := hwin Crow hCrow
  set Q : ℝ := holderErrorSpatialEntropy d with hQdef
  have hQ : 1 ≤ Q := holderErrorSpatialEntropy_one_le d
  refine ⟨Krow + Kw, 4 * Q * Cw, by positivity,
    by positivity, ?_⟩
  intro M s hs hs1 hbudget lambda hlambda L q m hq
  have hd0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg hd0 (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hlogpos : 0 < |Real.log M.delta| := abs_pos.mpr hlogNeg.ne
  have hbase : (0 : ℝ) < M.delta ^ 2 * |Real.log M.delta| := by positivity
  have hKrowBudget : Krow * M.delta ^ 2 * |Real.log M.delta| ≤ s := by
    refine le_trans ?_ hbudget
    have : Krow ≤ Krow + Kw := by linarith
    calc Krow * M.delta ^ 2 * |Real.log M.delta|
        = Krow * (M.delta ^ 2 * |Real.log M.delta|) := by ring
      _ ≤ (Krow + Kw) * (M.delta ^ 2 * |Real.log M.delta|) :=
          mul_le_mul_of_nonneg_right this hbase.le
      _ = (Krow + Kw) * M.delta ^ 2 * |Real.log M.delta| := by ring
  have hKwBudget : Kw * M.delta ^ 2 * |Real.log M.delta| ≤ s := by
    refine le_trans ?_ hbudget
    have : Kw ≤ Krow + Kw := by linarith
    calc Kw * M.delta ^ 2 * |Real.log M.delta|
        = Kw * (M.delta ^ 2 * |Real.log M.delta|) := by ring
      _ ≤ (Krow + Kw) * (M.delta ^ 2 * |Real.log M.delta|) :=
          mul_le_mul_of_nonneg_right this hbase.le
      _ = (Krow + Kw) * M.delta ^ 2 * |Real.log M.delta| := by ring
  set A : ℝ := Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s
    with hAdef
  have hA : 0 < A :=
    mul_pos (Real.exp_pos 1)
      (cutoffParameterizedResponseGammaScale_pos M hCrow hs)
  set Aw : ℝ := errorWindowScale M Cw s with hAwdef
  have hAw : 0 < Aw := errorWindowScale_pos M hCw hs
  have hSeq : errorSpatialScale d Aw =
      4 * Q * Cw * s ^ (-7 / 2 : ℝ) * M.delta *
        Real.sqrt |Real.log M.delta| := by
    rw [errorSpatialScale, hAwdef, errorWindowScale, hQdef]
    ring
  rw [← hSeq]
  exact measureReal_cutoffParameterizedErrorStoppingDepth_tail_le_ratio
    M L hs hs1 hA hAw (hrow M s hs hs1 hKrowBudget L)
    (fun n m hnm => hbounds M s hs hs1 hKwBudget n m hnm)
    (by rw [hSeq]; exact hlambda) q m hq

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
