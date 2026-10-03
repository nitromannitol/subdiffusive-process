module

public import SubdiffusiveProcess.Section6SumErrors.WindowBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ErrorStoppingAnalytic
@[expose] public section

/-!
# Analytic

Fixed-center Gaussian tails, the exact spatial grid union and absorption of spatial entropy for arbitrary order s.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d
/-- The optimized fixed-centre tail.  The `m+1-n` window length is retained
literally in the Gamma-two parameter; the threshold uses the manuscript gap
`m-n`. -/
theorem measureReal_accumulatedError_oneCenter_le_exp_rate
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Homogenization.Vec d)
    {C lambda : ℝ} (hC : 0 < C) {n m : ℕ} (hnm : n < m)
    (hrow : ∀ j : ℕ, Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) (holderResponseRow s M j)
      (Real.exp 1 * holderResponseGammaScale s M C))
    (hmeanRow : ∀ j : ℕ, ∫ ω, holderResponseRow s M j ω ∂M.P.toMeasure ≤ rowMeanCoeff s d C * M.delta)
    (hlambda : 4 * (tailWindowCoeff s d C * M.delta *
      Real.sqrt |Real.log M.delta|) ≤ lambda) :
    M.P.toMeasure.real {omega | lambda * ((m : ℝ) - (n : ℝ)) <
        ∑ k ∈ Finset.Icc n m,
          accumulatedError M none k z s omega} ≤
      Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) /
        (4 * (tailWindowCoeff s d C * M.delta *
          Real.sqrt |Real.log M.delta|))) ^ (2 : ℝ))) := by
  let A := tailWindowCoeff s d C * M.delta *
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
    exact mul_pos (mul_pos (tailWindowCoeff_pos s hs d C)
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
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (mul_pos (by norm_num) hA) hlambda
  have ht : 1 ≤ t := by
    rw [show t = lambda * Real.sqrt W / (4 * A) by rfl]
    rw [le_div_iff₀ (mul_pos (by norm_num) hA)]
    simpa only [one_mul] using (show 4 * A ≤ lambda * Real.sqrt W from calc
      4 * A ≤ lambda := hlambda
      _ ≤ lambda * Real.sqrt W :=
        le_mul_of_one_le_right hlambdaPos.le hsqrtW)
  obtain ⟨hmean, hfluct⟩ := window_bounds_log s hs hs1 M hC hnm.le
  have hmeanThreshold :
      accumulatedErrorWindowMeanBound s M
          (rowMeanCoeff s d C * M.delta) n m ≤
        lambda * gap / 2 := by
    calc
      _ ≤ W * A := by simpa only [W, A] using hmean
      _ ≤ (2 * gap) * A := mul_le_mul_of_nonneg_right hWle hA.le
      _ ≤ lambda * gap / 2 := by
        have hmul := mul_le_mul_of_nonneg_right hlambda hgap.le
        nlinarith
  have hsqrtSq : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hWpos.le
  have hfluctThreshold :
      accumulatedErrorWindowFluctuationScale s M
          (Real.exp 1 * holderResponseGammaScale s M C) n m * t ≤
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
  apply measureReal_accumulatedError_oneCenter_le_exp s hs hs1 M z hnm.le
    (mul_pos (Real.exp_pos 1) (holderResponseGammaScale_pos s hs M hC)) hrow (rowMeanCoeff s d C * M.delta) hmeanRow ht
  dsimp only [gap] at hmeanThreshold hfluctThreshold ⊢
  dsimp only [t, W, A]
  linarith

/-- Spatial union over the exact `3^(d(m-n))` grid centres. -/
theorem measureReal_accumulatedErrorSpatialFailure_le_card_mul_exp
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {C lambda : ℝ} (hC : 0 < C) {n m : ℕ} (hnm : n < m)
    (hrow : ∀ j : ℕ, Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) (holderResponseRow s M j)
      (Real.exp 1 * holderResponseGammaScale s M C))
    (hmeanRow : ∀ j : ℕ, ∫ ω, holderResponseRow s M j ω ∂M.P.toMeasure ≤ rowMeanCoeff s d C * M.delta)
    (hlambda : 4 * (tailWindowCoeff s d C * M.delta *
      Real.sqrt |Real.log M.delta|) ≤ lambda) :
    M.P.toMeasure.real
        (accumulatedErrorSpatialFailure M lambda s n m) ≤
      (3 ^ (d * (m - n)) : ℕ) *
        Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) /
          (4 * (tailWindowCoeff s d C * M.delta *
            Real.sqrt |Real.log M.delta|))) ^ (2 : ℝ))) := by
  let centers := gridCentersInCube d n m
  let E : Homogenization.Vec d → Set (Sample d) := fun z =>
    {omega | lambda * ((m : ℝ) - (n : ℝ)) <
      ∑ k ∈ Finset.Icc n m,
        accumulatedError M none k z s omega}
  have hevent : accumulatedErrorSpatialFailure M lambda s n m =
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
          (4 * (tailWindowCoeff s d C * M.delta *
            Real.sqrt |Real.log M.delta|))) ^ (2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro z _hz
      exact measureReal_accumulatedError_oneCenter_le_exp_rate
        s hs hs1 M z hC hnm hrow hmeanRow hlambda
    _ = (3 ^ (d * (m - n)) : ℕ) *
        Real.exp (-((lambda * Real.sqrt ((m + 1 - n : ℕ) : ℝ) /
          (4 * (tailWindowCoeff s d C * M.delta *
            Real.sqrt |Real.log M.delta|))) ^ (2 : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_gridCentersInCube hnm.le]

/-- Spatial-entropy coefficient multiplying the logarithm-absorbed window scale. -/
def spatialCoeff (s : ℝ) (d : ℕ) (C : ℝ) : ℝ :=
  4 * holderErrorSpatialEntropy d * tailWindowCoeff s d C

/-- The centre entropy is absorbed into the Gaussian exponent.  The free
parameter `u` is the eventual Gamma-one tail parameter. -/
theorem measureReal_accumulatedErrorSpatialFailure_le_exp
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {C lambda u : ℝ} (hC : 0 < C) (hu : 1 ≤ u)
    {n m : ℕ} (hnm : n < m)
    (hrow : ∀ j : ℕ, Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) (holderResponseRow s M j)
      (Real.exp 1 * holderResponseGammaScale s M C))
    (hmeanRow : ∀ j : ℕ, ∫ ω, holderResponseRow s M j ω ∂M.P.toMeasure ≤ rowMeanCoeff s d C * M.delta)
    (hlambda : spatialCoeff s d C * M.delta *
      Real.sqrt |Real.log M.delta| * u ≤ lambda) :
    M.P.toMeasure.real
        (accumulatedErrorSpatialFailure M lambda s n m) ≤
      Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ)))) := by
  let A := tailWindowCoeff s d C * M.delta *
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
    exact mul_pos (mul_pos (tailWindowCoeff_pos s hs d C)
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
      all_goals dsimp only [spatialCoeff, A, Q]
      all_goals ring_nf
    linarith
  have htLower : Q * u * Real.sqrt W ≤ t := by
    rw [show t = lambda * Real.sqrt W / (4 * A) by rfl]
    rw [le_div_iff₀ (mul_pos (by norm_num) hA)]
    have hmul := mul_le_mul_of_nonneg_right
      (show 4 * A * (Q * u) ≤ lambda from by
        have hgiven : 4 * Q * A * u ≤ lambda := by
          convert hlambda using 1
          all_goals dsimp only [spatialCoeff, A, Q]
          all_goals ring_nf
        convert hgiven using 1
        all_goals ring_nf)
      hsqrtW0
    convert hmul using 1
    all_goals ring_nf
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have ht0 : 0 ≤ t := (mul_nonneg (mul_nonneg hQ0 hu0) hsqrtW0).trans htLower
  have hQsq : Q ^ 2 = 2 * (d : ℝ) * Real.log 3 + 1 := by
    dsimp only [Q, holderErrorSpatialEntropy]
    exact Real.sq_sqrt (by
      have hlog : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
      positivity)
  have hWsq : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hW0
  have htSq : (Q * u * Real.sqrt W) ^ 2 ≤ t ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (mul_nonneg hQ0 hu0) hsqrtW0) ht0).2 htLower
  have hrate : (d : ℝ) * Real.log 3 * gap - t ^ 2 ≤ -(u ^ 2 * gap) := by
    have hdlog : 0 ≤ (d : ℝ) * Real.log 3 := by positivity
    have huSq : 1 ≤ u ^ 2 := by nlinarith
    rw [mul_pow, mul_pow, hQsq, hWsq] at htSq
    have hgapW := mul_le_mul_of_nonneg_left hWgap
      (mul_nonneg (by positivity : 0 ≤ 2 * (d : ℝ) * Real.log 3 + 1)
        (sq_nonneg u))
    nlinarith [mul_nonneg hdlog (sub_nonneg.mpr huSq)]
  have hcardExp : ((3 ^ (d * (m - n)) : ℕ) : ℝ) =
      Real.exp ((d : ℝ) * Real.log 3 * gap) := by
    have hexponent : (((d * (m - n) : ℕ) : ℝ) * Real.log 3) =
        (d : ℝ) * Real.log 3 * gap := by
      dsimp only [gap]
      rw [Nat.cast_mul, Nat.cast_sub hnm.le]
      ring
    rw [← hexponent, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have hraw := measureReal_accumulatedErrorSpatialFailure_le_card_mul_exp
    s hs hs1 M hC hnm hrow hmeanRow hlambda'
  calc
    M.P.toMeasure.real
        (accumulatedErrorSpatialFailure M lambda s n m) ≤
      ((3 ^ (d * (m - n)) : ℕ) : ℝ) * Real.exp (-(t ^ (2 : ℝ))) := by
        simpa only [t, A, W] using hraw
    _ = Real.exp ((d : ℝ) * Real.log 3 * gap - t ^ 2) := by
      rw [hcardExp, ← Real.exp_add]
      congr 1
      rw [show t ^ (2 : ℝ) = t ^ 2 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
      ring
    _ ≤ Real.exp (-(u ^ 2 * gap)) := Real.exp_le_exp.mpr hrate
    _ = _ := by rfl

end
end SubdiffusiveProcess.Section6SumErrors.Response
