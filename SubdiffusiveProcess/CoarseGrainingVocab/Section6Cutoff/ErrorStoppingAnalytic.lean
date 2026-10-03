module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ErrorStoppingDepthTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ErrorStoppingAnalytic

@[expose] public section

/-!
# Analytic tail for the finite-cutoff accumulated-error stopping depth

The numerical absorption is identical to the uncutoff argument because the
finite-cutoff response window was assembled at the same Gamma-two scale.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Optimized finite-cutoff fixed-centre tail. -/
theorem measureReal_cutoffAccumulatedError_oneCenter_le_exp_rate
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    {C lambda : ℝ} (hC : 0 < C) {n m : ℕ} (hnm : n < m)
    (hrow : ∀ j : ℕ, Homogenization.IndependentSums.IsBigOWith
      M.P.toMeasure (Homogenization.IndependentSums.gammaSigma 2)
      (cutoffHolderResponseRow M L j)
      (Real.exp 1 * holderResponseGammaScale M C))
    (hlambda : 4 * (holderErrorWindowCoeff d C * M.delta *
      Real.sqrt |Real.log M.delta|) ≤ lambda) :
    M.P.toMeasure.real {omega | lambda * ((m : ℝ) - (n : ℝ)) <
        ∑ k ∈ Finset.Icc n m,
          accumulatedError M (some L) k z holderStoppingS omega} ≤
      Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) /
        (4 * (holderErrorWindowCoeff d C * M.delta *
          Real.sqrt |Real.log M.delta|))) ^ (2 : ℝ))) := by
  let A := holderErrorWindowCoeff d C * M.delta *
    Real.sqrt |Real.log M.delta|
  let W : ℝ := ((m + 1 - n : ℕ) : ℝ)
  let gap : ℝ := (m : ℝ) - (n : ℝ)
  let t := lambda * Real.sqrt W / (4 * A)
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hroot : 0 < Real.sqrt |Real.log M.delta| :=
    Real.sqrt_pos.mpr (abs_pos.mpr hlogNeg.ne)
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos (holderErrorWindowCoeff_pos d C)
      M.shellPrefix.delta_pos) hroot
  have hgapNat : 0 < m - n := Nat.sub_pos_of_lt hnm
  have hgap : 0 < gap := by
    dsimp only [gap]
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hWnat : m + 1 - n = (m - n) + 1 := by omega
  have hW : W = gap + 1 := by
    dsimp only [W, gap]
    rw [hWnat, Nat.cast_add, Nat.cast_one, Nat.cast_sub (Nat.le_of_lt hnm)]
  have hgapOne : 1 ≤ gap := by
    have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hnm)
    dsimp only [gap]
    linarith
  have hWpos : 0 < W := by rw [hW]; linarith
  have hWle : W ≤ 2 * gap := by rw [hW]; linarith
  have hsqrtW : 1 ≤ Real.sqrt W := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    rw [hW]
    linarith
  have hlambdaPos : 0 < lambda :=
    lt_of_lt_of_le (mul_pos (by norm_num) hA) hlambda
  have ht : 1 ≤ t := by
    rw [show t = lambda * Real.sqrt W / (4 * A) by rfl]
    rw [le_div_iff₀ (mul_pos (by norm_num) hA)]
    simpa only [one_mul] using (show 4 * A ≤ lambda * Real.sqrt W from calc
      4 * A ≤ lambda := hlambda
      _ ≤ lambda * Real.sqrt W :=
        le_mul_of_one_le_right hlambdaPos.le hsqrtW)
  obtain ⟨hmean, hfluct⟩ := accumulatedErrorWindow_bounds M hC hnm.le
  have hmeanThreshold :
      accumulatedErrorWindowMeanBound M
          (Real.exp 1 * holderResponseGammaScale M C) n m ≤
        lambda * gap / 2 := by
    calc
      _ ≤ W * A := by simpa only [W, A] using hmean
      _ ≤ (2 * gap) * A := mul_le_mul_of_nonneg_right hWle hA.le
      _ ≤ lambda * gap / 2 := by
        have hmul := mul_le_mul_of_nonneg_right hlambda hgap.le
        nlinarith
  have hsqrtSq : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hWpos.le
  have hfluctThreshold :
      accumulatedErrorWindowFluctuationScale M
          (Real.exp 1 * holderResponseGammaScale M C) n m * t ≤
        lambda * gap / 2 := by
    calc
      _ ≤ (A * Real.sqrt W) * t :=
        mul_le_mul_of_nonneg_right (by simpa only [A, W] using hfluct)
          (zero_le_one.trans ht)
      _ = lambda * W / 4 := by
        dsimp only [t]
        field_simp [hA.ne']
        nlinarith [hsqrtSq]
      _ ≤ lambda * gap / 2 := by
        have := mul_le_mul_of_nonneg_left hWle hlambdaPos.le
        nlinarith
  apply measureReal_cutoffAccumulatedError_oneCenter_le_exp
    M L z hnm.le
    (mul_pos (Real.exp_pos 1) (holderResponseGammaScale_pos M hC)) hrow ht
  dsimp only [gap] at hmeanThreshold hfluctThreshold ⊢
  dsimp only [t, W, A]
  linarith

/-- Spatial union over the exact cutoff grid centres. -/
theorem measureReal_cutoffAccumulatedErrorSpatialFailure_le_card_mul_exp
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {C lambda : ℝ} (hC : 0 < C) {n m : ℕ} (hnm : n < m)
    (hrow : ∀ j : ℕ, Homogenization.IndependentSums.IsBigOWith
      M.P.toMeasure (Homogenization.IndependentSums.gammaSigma 2)
      (cutoffHolderResponseRow M L j)
      (Real.exp 1 * holderResponseGammaScale M C))
    (hlambda : 4 * (holderErrorWindowCoeff d C * M.delta *
      Real.sqrt |Real.log M.delta|) ≤ lambda) :
    M.P.toMeasure.real
        (cutoffAccumulatedErrorSpatialFailure M L lambda holderStoppingS n m) ≤
      (3 ^ (d * (m - n)) : ℕ) *
        Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) /
          (4 * (holderErrorWindowCoeff d C * M.delta *
            Real.sqrt |Real.log M.delta|))) ^ (2 : ℝ))) := by
  let centers := gridCentersInCube d n m
  let E : Vec d → Set (Sample d) := fun z =>
    {omega | lambda * ((m : ℝ) - (n : ℝ)) <
      ∑ k ∈ Finset.Icc n m,
        accumulatedError M (some L) k z holderStoppingS omega}
  have hevent :
      cutoffAccumulatedErrorSpatialFailure M L lambda holderStoppingS n m =
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
        Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) /
          (4 * (holderErrorWindowCoeff d C * M.delta *
            Real.sqrt |Real.log M.delta|))) ^ (2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro z _hz
      exact measureReal_cutoffAccumulatedError_oneCenter_le_exp_rate
        M L z hC hnm hrow hlambda
    _ = (3 ^ (d * (m - n)) : ℕ) *
        Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) /
          (4 * (holderErrorWindowCoeff d C * M.delta *
            Real.sqrt |Real.log M.delta|))) ^ (2 : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_gridCentersInCube hnm.le]

/-- The grid-centre entropy is absorbed into the finite-cutoff Gaussian
window exponent. -/
theorem measureReal_cutoffAccumulatedErrorSpatialFailure_le_exp
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {C lambda u : ℝ} (hC : 0 < C) (hu : 1 ≤ u)
    {n m : ℕ} (hnm : n < m)
    (hrow : ∀ j : ℕ, Homogenization.IndependentSums.IsBigOWith
      M.P.toMeasure (Homogenization.IndependentSums.gammaSigma 2)
      (cutoffHolderResponseRow M L j)
      (Real.exp 1 * holderResponseGammaScale M C))
    (hlambda : holderErrorSpatialCoeff d C * M.delta *
      Real.sqrt |Real.log M.delta| * u ≤ lambda) :
    M.P.toMeasure.real
        (cutoffAccumulatedErrorSpatialFailure M L lambda holderStoppingS n m) ≤
      Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ)))) := by
  let A := holderErrorWindowCoeff d C * M.delta *
    Real.sqrt |Real.log M.delta|
  let Q := holderErrorSpatialEntropy d
  let W : ℝ := ((m + 1 - n : ℕ) : ℝ)
  let gap : ℝ := (m : ℝ) - (n : ℝ)
  let t := lambda * Real.sqrt W / (4 * A)
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hroot : 0 < Real.sqrt |Real.log M.delta| :=
    Real.sqrt_pos.mpr (abs_pos.mpr hlogNeg.ne)
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos (holderErrorWindowCoeff_pos d C)
      M.shellPrefix.delta_pos) hroot
  have hQ : 1 ≤ Q := holderErrorSpatialEntropy_one_le d
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hgap : 0 < gap := by
    dsimp only [gap]
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hWgap : gap ≤ W := by
    dsimp only [gap, W]
    rw [show m + 1 - n = (m - n) + 1 by omega,
      Nat.cast_add, Nat.cast_one, Nat.cast_sub hnm.le]
    linarith
  have hW0 : 0 ≤ W := hgap.le.trans hWgap
  have hsqrtW0 : 0 ≤ Real.sqrt W := Real.sqrt_nonneg _
  have hlambda' : 4 * A ≤ lambda := by
    have hsmall : 4 * A * 1 ≤ 4 * Q * A * u := by
      have hQA : 0 ≤ 4 * A := by positivity
      calc
        4 * A * 1 ≤ 4 * A * Q := mul_le_mul_of_nonneg_left hQ hQA
        _ ≤ 4 * A * Q * u := le_mul_of_one_le_right (by positivity) hu
        _ = 4 * Q * A * u := by ring
    have hgiven : 4 * Q * A * u ≤ lambda := by
      convert hlambda using 1
      all_goals dsimp only [holderErrorSpatialCoeff, A, Q]
      all_goals ring_nf
    linarith
  have htLower : Q * u * Real.sqrt W ≤ t := by
    rw [show t = lambda * Real.sqrt W / (4 * A) by rfl]
    rw [le_div_iff₀ (mul_pos (by norm_num) hA)]
    have hmul := mul_le_mul_of_nonneg_right
      (show 4 * A * (Q * u) ≤ lambda from by
        have hgiven : 4 * Q * A * u ≤ lambda := by
          convert hlambda using 1
          all_goals dsimp only [holderErrorSpatialCoeff, A, Q]
          all_goals ring_nf
        convert hgiven using 1
        all_goals ring_nf)
      hsqrtW0
    convert hmul using 1
    all_goals ring_nf
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have ht0 : 0 ≤ t :=
    (mul_nonneg (mul_nonneg hQ0 hu0) hsqrtW0).trans htLower
  have hQsq : Q ^ 2 = 2 * (d : ℝ) * Real.log 3 + 1 := by
    dsimp only [Q, holderErrorSpatialEntropy]
    exact Real.sq_sqrt (by
      have hlog : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
      positivity)
  have hWsq : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hW0
  have htSq : (Q * u * Real.sqrt W) ^ 2 ≤ t ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (mul_nonneg hQ0 hu0) hsqrtW0) ht0).2 htLower
  have hrate : (d : ℝ) * Real.log 3 * gap - t ^ 2 ≤
      -(u ^ 2 * gap) := by
    have hdlog : 0 ≤ (d : ℝ) * Real.log 3 := by positivity
    have huSq : 1 ≤ u ^ 2 := by nlinarith
    rw [mul_pow, mul_pow, hQsq, hWsq] at htSq
    have hgapW := mul_le_mul_of_nonneg_left hWgap
      (mul_nonneg (by positivity : 0 ≤ 2 * (d : ℝ) * Real.log 3 + 1)
        (sq_nonneg u))
    nlinarith [mul_nonneg hdlog (sub_nonneg.mpr huSq)]
  have hcardExp : (((3 ^ (d * (m - n)) : ℕ) : ℝ)) =
      Real.exp ((d : ℝ) * Real.log 3 * gap) := by
    have hexponent : (((d * (m - n) : ℕ) : ℝ) * Real.log 3) =
        (d : ℝ) * Real.log 3 * gap := by
      dsimp only [gap]
      rw [Nat.cast_mul, Nat.cast_sub hnm.le]
      ring
    rw [← hexponent, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have hraw := measureReal_cutoffAccumulatedErrorSpatialFailure_le_card_mul_exp
    M L hC hnm hrow hlambda'
  calc
    M.P.toMeasure.real
        (cutoffAccumulatedErrorSpatialFailure M L lambda holderStoppingS n m) ≤
      ((3 ^ (d * (m - n)) : ℕ) : ℝ) * Real.exp (-(t ^ (2 : ℝ))) := by
        simpa only [t, A, W] using hraw
    _ = Real.exp ((d : ℝ) * Real.log 3 * gap - t ^ 2) := by
      rw [hcardExp, ← Real.exp_add]
      congr 1
      rw [show t ^ (2 : ℝ) = t ^ 2 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]]
      ring
    _ ≤ Real.exp (-(u ^ 2 * gap)) := Real.exp_le_exp.mpr hrate
    _ = _ := by rfl

theorem cutoffErrorStoppingDepth_le_succ {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (lambda s : ℝ)
    (m : ℕ) (omega : Sample d) :
    cutoffErrorStoppingDepth M L lambda s m omega ≤ m + 1 := by
  have hlower := (errorStoppingIndex M (some L) lambda s m omega).property.1
  have hupper := (errorStoppingIndex M (some L) lambda s m omega).property.2
  have hnonneg : 0 ≤ (m : ℤ) -
      (errorStoppingIndex M (some L) lambda s m omega : ℤ) := by omega
  unfold cutoffErrorStoppingDepth
  rw [Int.toNat_le]
  push_cast
  omega

/-- Starting-scale union before summing the cutoff geometric tail. -/
theorem measureReal_cutoffErrorStoppingDepth_tail_le_sum_exp
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {C lambda u : ℝ} (hC : 0 < C) (hu : 1 ≤ u)
    (hrow : ∀ j : ℕ, Homogenization.IndependentSums.IsBigOWith
      M.P.toMeasure (Homogenization.IndependentSums.gammaSigma 2)
      (cutoffHolderResponseRow M L j)
      (Real.exp 1 * holderResponseGammaScale M C))
    (hlambda : holderErrorSpatialCoeff d C * M.delta *
      Real.sqrt |Real.log M.delta| * u ≤ lambda)
    {q m : ℕ} (hq : 0 < q) (hqm : q ≤ m) :
    M.P.toMeasure.real {omega |
        q < cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} ≤
      ∑ n ∈ Finset.range (m - q + 1),
        Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ)))) := by
  have hsubset := cutoffErrorStoppingDepth_tail_subset_iUnion
    M L lambda holderStoppingS q m hq
  calc
    M.P.toMeasure.real {omega |
        q < cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} ≤
      M.P.toMeasure.real (⋃ n ∈ Finset.range (m - q + 1),
        cutoffAccumulatedErrorSpatialFailure M L lambda holderStoppingS n m) := by
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (MeasureTheory.measure_mono hsubset)
    _ ≤ ∑ n ∈ Finset.range (m - q + 1),
        M.P.toMeasure.real
          (cutoffAccumulatedErrorSpatialFailure M L lambda holderStoppingS n m) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.range (m - q + 1),
        Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ)))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnlt : n < m := by
        rw [Finset.mem_range] at hn
        omega
      exact measureReal_cutoffAccumulatedErrorSpatialFailure_le_exp
        M L hC hu hnlt hrow hlambda

/-- Gamma-one tail of the finite-cutoff accumulated-error stopping depth. -/
theorem measureReal_cutoffErrorStoppingDepth_tail_le_gammaOne
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {C lambda u : ℝ} (hC : 0 < C) (hu : 1 ≤ u)
    (hrow : ∀ j : ℕ, Homogenization.IndependentSums.IsBigOWith
      M.P.toMeasure (Homogenization.IndependentSums.gammaSigma 2)
      (cutoffHolderResponseRow M L j)
      (Real.exp 1 * holderResponseGammaScale M C))
    (hlambda : holderErrorSpatialCoeff d C * M.delta *
      Real.sqrt |Real.log M.delta| * u ≤ lambda)
    (q m : ℕ) (hq : 0 < q) :
    M.P.toMeasure.real {omega |
        q < cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} ≤
      holderGammaOneGeometricConst *
        Real.exp (-(u ^ 2 * max ((q : ℝ) - 1) 0)) := by
  by_cases hqm : q ≤ m
  · have hsum := measureReal_cutoffErrorStoppingDepth_tail_le_sum_exp
      M L hC hu hrow hlambda hq hqm
    have hgeom := sum_reverse_exp_neg_u_sq_gap_le hu q m hqm
    have hqOne : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
    have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hqOne
    rw [max_eq_left (by linarith : 0 ≤ (q : ℝ) - 1)]
    exact hsum.trans hgeom
  · have hevent : {omega |
        q < cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} = ∅ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt_of_ge
        ((cutoffErrorStoppingDepth_le_succ M L lambda holderStoppingS m omega).trans
          (by omega : m + 1 ≤ q))
    rw [hevent]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact mul_nonneg holderGammaOneGeometricConst_pos.le (Real.exp_pos _).le

/-- Optimized finite-cutoff Gamma-one form in the physical threshold. -/
theorem measureReal_cutoffErrorStoppingDepth_tail_le_exp_ratio
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {C lambda : ℝ} (hC : 0 < C)
    (hrow : ∀ j : ℕ, Homogenization.IndependentSums.IsBigOWith
      M.P.toMeasure (Homogenization.IndependentSums.gammaSigma 2)
      (cutoffHolderResponseRow M L j)
      (Real.exp 1 * holderResponseGammaScale M C))
    (hlambda : holderErrorSpatialCoeff d C * M.delta *
      Real.sqrt |Real.log M.delta| ≤ lambda)
    (q m : ℕ) (hq : 0 < q) :
    M.P.toMeasure.real {omega |
        q < cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} ≤
      holderGammaOneGeometricConst * Real.exp
        (-(lambda ^ 2 * max ((q : ℝ) - 1) 0 /
          (holderErrorSpatialCoeff d C ^ 2 * M.delta ^ 2 *
            |Real.log M.delta|))) := by
  let A := holderErrorSpatialCoeff d C * M.delta *
    Real.sqrt |Real.log M.delta|
  let u := lambda / A
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hlogAbs : 0 < |Real.log M.delta| := abs_pos.mpr hlogNeg.ne
  have hroot : 0 < Real.sqrt |Real.log M.delta| :=
    Real.sqrt_pos.mpr hlogAbs
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos (holderErrorSpatialCoeff_pos d C)
      M.shellPrefix.delta_pos) hroot
  have hu : 1 ≤ u := by
    dsimp only [u]
    exact (le_div_iff₀ hA).2 (by simpa only [one_mul, A] using hlambda)
  have hscaled : holderErrorSpatialCoeff d C * M.delta *
      Real.sqrt |Real.log M.delta| * u ≤ lambda := by
    dsimp only [u, A]
    field_simp [holderErrorSpatialCoeff_pos d C |>.ne',
      M.shellPrefix.delta_pos.ne', hroot.ne']
    exact le_rfl
  have htail := measureReal_cutoffErrorStoppingDepth_tail_le_gammaOne
    M L hC hu hrow hscaled q m hq
  convert htail using 1
  congr 2
  have hsqrtSq := Real.sq_sqrt hlogAbs.le
  dsimp only [u, A]
  field_simp [holderErrorSpatialCoeff_pos d C |>.ne',
    M.shellPrefix.delta_pos.ne', hlogAbs.ne', hroot.ne']
  rw [hsqrtSq]

/-- Dimension-only response-row choice and the optimized finite-cutoff
stopping tail, uniformly in `L`. -/
theorem exists_cutoffErrorStoppingDepth_tail {d : ℕ} [NeZero d] :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ K⁻¹ →
      ∀ lambda : ℝ,
        holderErrorSpatialCoeff d C * M.delta *
            Real.sqrt |Real.log M.delta| ≤ lambda →
        ∀ L q m : ℕ, 0 < q →
          M.P.toMeasure.real {omega |
              q < cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} ≤
            holderGammaOneGeometricConst * Real.exp
              (-(lambda ^ 2 * max ((q : ℝ) - 1) 0 /
                (holderErrorSpatialCoeff d C ^ 2 * M.delta ^ 2 *
                  |Real.log M.delta|))) := by
  obtain ⟨K, C, hK, hC, hrow⟩ :=
    exists_isBigOWith_gammaTwo_cutoffHolderResponseRow_of_delta_small (d := d)
  refine ⟨K, C, hK, hC, ?_⟩
  intro M hdelta lambda hlambda L q m hq
  exact measureReal_cutoffErrorStoppingDepth_tail_le_exp_ratio
    M L hC (hrow M hdelta L) hlambda q m hq

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
