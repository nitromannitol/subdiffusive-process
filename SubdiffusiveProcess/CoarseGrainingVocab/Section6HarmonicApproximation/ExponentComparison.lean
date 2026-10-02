import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.StabilityIndexCube
import Homogenization.Book.Ch02.Theorems.HomogenizationError.InfinityOne
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public

/-!
# Scale-exponent comparisons for harmonic approximation

This is the Jensen layer used in the proof of
`l.harmonic.approximation.good.scales.GMC`.  At the paired indices
`(u, q = 1)` and `(u / 2, q = 2)`, the geometric weights coincide.  The
`q = 1` response error and the two `q = 1` coarse ellipticity quantities are
therefore bounded by their `q = 2` counterparts.

PROVENANCE: this decomposition mirrors
`Algsuperdiff/Section4/Provider/ExcessDecay/StabilityExponentComparison.lean`
and the first section of
`Algsuperdiff/Section4/Provider/ExcessDecay/CaccioppoliInteriorPrefactor.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ} [NeZero d]

private theorem geometricWeight_two_half (u : ℝ) (n : ℕ) :
    Ch02.geometricWeight (u / 2) 2 n = Ch02.geometricWeight u 1 n := by
  have h := Homogenization.geometricWeight_eq_mul_one (u / 2) 2 n
  rw [show u / 2 * 2 = u by ring] at h
  simpa only [Ch02.geometricWeight_eq_old] using h

private theorem homogenizationError_sq_eq_tsum_weight_mul_sq
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d)
    {u : ℝ} (hu : 0 < u) :
    HomogenizationErrorOnCube Q (u / 2) .infinity (.finite 2) a a0 ^ 2 =
      ∑' n : ℕ, Ch02.geometricWeight u 1 n *
        scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0 ^ 2 := by
  rw [homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q
    (by linarith only [hu] : 0 < u / 2) a a0]
  refine tsum_congr fun n => ?_
  rw [geometricWeight_two_half u n,
    scaleResponseAtScale_infinity_sq_eq Q
      (sub_le_self _ (Int.natCast_nonneg n)) a a0]

private theorem summable_weight_mul_response_sq
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d)
    {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ => Ch02.geometricWeight u 1 n *
      scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0 ^ 2 := by
  have hbase : Summable fun n : ℕ => Homogenization.geometricWeight u 1 n *
      maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a a0 :=
    Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := u) (q := 1) (C := normalizedBlockResponseUniformBound Q a a0)
      (by linarith only [hu])
      (fun n => maxDescendantNormalizedBlockResponseAtScale_nonneg Q
        (sub_le_self _ (Int.natCast_nonneg n)) a a0)
      (fun n => maxDescendantNormalizedBlockResponseAtScale_le_uniform Q
        (sub_le_self _ (Int.natCast_nonneg n)) a a0)
  refine hbase.congr fun n => ?_
  rw [Ch02.geometricWeight_eq_old,
    scaleResponseAtScale_infinity_sq_eq Q
      (sub_le_self _ (Int.natCast_nonneg n)) a a0]

/-- The displayed `q = 1 ← q = 2` comparison for the homogenization error:
`ℰ_{u,∞,1} ≤ ℰ_{u/2,∞,2}`. -/
theorem homogenizationError_infinity_one_le_two_half
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d)
    {u : ℝ} (hu : 0 < u) :
    HomogenizationErrorOnCube Q u .infinity (.finite 1) a a0 ≤
      HomogenizationErrorOnCube Q (u / 2) .infinity (.finite 2) a a0 := by
  classical
  set A : ℝ := HomogenizationErrorOnCube Q (u / 2) .infinity (.finite 2) a a0
  set W : ℕ → ℝ := fun n => Ch02.geometricWeight u 1 n
  set R : ℕ → ℝ := fun n =>
    scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0
  have hWpos : ∀ n, 0 < W n := by
    intro n
    simpa [W, Ch02.geometricWeight_eq_old] using
      Homogenization.geometricWeight_pos (s := u) (q := 1) n
        (by linarith only [hu])
  have hWsum : Summable W := by
    simpa [W, Ch02.geometricWeight_eq_old] using
      Homogenization.summable_geometricWeight (s := u) (q := 1)
        (by linarith only [hu])
  have hWone : ∑' n, W n = 1 := by
    simpa [W, Ch02.geometricWeight_eq_old] using
      Homogenization.tsum_geometricWeight_eq_one (s := u) (q := 1)
        (by linarith only [hu])
  have hRnonneg : ∀ n, 0 ≤ R n := fun n =>
    scaleResponseAtScale_infinity_nonneg Q
      (sub_le_self _ (Int.natCast_nonneg n)) a a0
  have hAnonneg : 0 ≤ A :=
    LambdaStabilitySupport.homogenizationErrorOnCube_infinity_two_nonneg Q a a0
      (by linarith only [hu] : 0 < u / 2)
  have hAsq : A ^ 2 = ∑' n, W n * R n ^ 2 := by
    simpa [A, W, R] using
      homogenizationError_sq_eq_tsum_weight_mul_sq Q a a0 hu
  have hsumSq : Summable fun n => W n * R n ^ 2 := by
    simpa [W, R] using summable_weight_mul_response_sq Q a a0 hu
  have hsumOne : Summable fun n => W n * R n := by
    simpa [W, R, Ch02.geometricWeight_eq_old] using
      Ch02.summable_homogenizationErrorOnCube_infinity_one_terms Q a a0 hu
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum Q u a a0]
  change ∑' n, W n * R n ≤ A
  rcases eq_or_lt_of_le hAnonneg with hA0 | hApos
  · have hzero : ∀ n, W n * R n ^ 2 = 0 := by
      intro n
      have hle : W n * R n ^ 2 ≤ ∑' k, W k * R k ^ 2 :=
        hsumSq.le_tsum n fun k _ => mul_nonneg (hWpos k).le (sq_nonneg _)
      have hsum0 : ∑' k, W k * R k ^ 2 = 0 := by
        rw [← hAsq, ← hA0]
        norm_num
      have hnn : 0 ≤ W n * R n ^ 2 :=
        mul_nonneg (hWpos n).le (sq_nonneg _)
      linarith only [hle, hsum0, hnn]
    have hR0 : ∀ n, R n = 0 := by
      intro n
      rcases mul_eq_zero.mp (hzero n) with hw | hr
      · exact False.elim ((hWpos n).ne' hw)
      · exact eq_zero_of_pow_eq_zero hr
    have hfun : (fun n => W n * R n) = fun _ => 0 := by
      funext n
      rw [hR0 n, mul_zero]
    rw [hfun, tsum_zero, ← hA0]
  · have hcomp : Summable fun n =>
        (2 * A)⁻¹ * (W n * R n ^ 2) + A / 2 * W n :=
      (hsumSq.mul_left _).add (hWsum.mul_left _)
    have hterm : ∀ n,
        W n * R n ≤ (2 * A)⁻¹ * (W n * R n ^ 2) + A / 2 * W n := by
      intro n
      have hkey : 2 * A * R n ≤ R n ^ 2 + A ^ 2 := by
        nlinarith only [sq_nonneg (R n - A)]
      have hmul : W n * (2 * A * R n) ≤ W n * (R n ^ 2 + A ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (hWpos n).le
      have htwoA : 0 < 2 * A := by positivity
      refine le_of_mul_le_mul_left ?_ htwoA
      have hexp : 2 * A *
          ((2 * A)⁻¹ * (W n * R n ^ 2) + A / 2 * W n) =
          W n * R n ^ 2 + A ^ 2 * W n := by
        field_simp
      rw [hexp]
      linarith only [hmul]
    have hle := Summable.tsum_le_tsum hterm hsumOne hcomp
    have hval : ∑' n,
        ((2 * A)⁻¹ * (W n * R n ^ 2) + A / 2 * W n) = A := by
      rw [Summable.tsum_add (hsumSq.mul_left _) (hWsum.mul_left _),
        hsumSq.tsum_mul_left, hWsum.tsum_mul_left, hWone, ← hAsq]
      field_simp
      ring
    linarith only [hle, hval]

private theorem LambdaSq_finite_two_eq_tsum
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {u : ℝ} (hu : 0 < u) :
    Ch02.LambdaSq Q u (.finite 2) a =
      ∑' n : ℕ, Ch02.geometricWeight u 2 n *
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
  have h := Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q u 2 a
    (by norm_num) (by positivity)
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at h
  simpa only [Real.rpow_eq_pow, Real.rpow_one] using h

private theorem lambdaSq_finite_two_inv_eq_tsum
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {u : ℝ} (hu : 0 < u) :
    (Ch02.lambdaSq Q u (.finite 2) a)⁻¹ =
      ∑' n : ℕ, Ch02.geometricWeight u 2 n *
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) a := by
  have h := Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q u 2 a
    (by norm_num) (by positivity)
  rw [show (-2 : ℝ) / 2 = -1 by norm_num,
    show (2 : ℝ) / 2 = 1 by norm_num] at h
  simpa only [Real.rpow_eq_pow, Real.rpow_neg_one, Real.rpow_one] using h

/-- The displayed upper-ellipticity comparison
`Λ_{u,1} ≤ Λ_{u/2,2}`. -/
theorem LambdaSq_finite_one_le_two_half
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {u : ℝ} (hu : 0 < u) :
    Ch02.LambdaSq Q u (.finite 1) a ≤
      Ch02.LambdaSq Q (u / 2) (.finite 2) a := by
  have h :=
    Ch02.LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale
      Q a hu
  rw [LambdaSq_finite_two_eq_tsum Q a
    (by linarith only [hu] : 0 < u / 2)]
  refine h.trans (le_of_eq (tsum_congr fun n => ?_))
  rw [geometricWeight_two_half]

/-- The displayed inverse lower-ellipticity comparison
`λ_{u,1}⁻¹ ≤ λ_{u/2,2}⁻¹`. -/
theorem lambdaSq_finite_one_inv_le_two_half
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {u : ℝ} (hu : 0 < u) :
    (Ch02.lambdaSq Q u (.finite 1) a)⁻¹ ≤
      (Ch02.lambdaSq Q (u / 2) (.finite 2) a)⁻¹ := by
  have h :=
    Ch02.lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
      Q a hu
  rw [lambdaSq_finite_two_inv_eq_tsum Q a
    (by linarith only [hu] : 0 < u / 2)]
  refine h.trans (le_of_eq (tsum_congr fun n => ?_))
  rw [geometricWeight_two_half]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
