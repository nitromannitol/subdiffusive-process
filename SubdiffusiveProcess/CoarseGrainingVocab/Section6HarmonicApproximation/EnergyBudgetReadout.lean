module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.EnergyReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyRowScalar

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section

/-- A square root of four nonnegative squares is bounded by their sum. -/
theorem sqrt_four_sq_le_sum {A B F H : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hF : 0 ≤ F) (hH : 0 ≤ H) :
    Real.sqrt (A ^ 2 + B ^ 2 + F ^ 2 + H ^ 2) ≤ A + B + F + H := by
  have hAB : 0 ≤ A ^ 2 + B ^ 2 := by positivity
  have hF2 : 0 ≤ F ^ 2 := sq_nonneg F
  have hH2 : 0 ≤ H ^ 2 := sq_nonneg H
  calc
    Real.sqrt (A ^ 2 + B ^ 2 + F ^ 2 + H ^ 2) ≤
        Real.sqrt (A ^ 2 + B ^ 2) + Real.sqrt (F ^ 2) + Real.sqrt (H ^ 2) := by
      have houter :=
        Section6HolderInterior.sqrt_add_le_add_sqrt (add_nonneg hAB hF2) hH2
      have hinner := Section6HolderInterior.sqrt_add_le_add_sqrt hAB hF2
      linarith
    _ ≤ (Real.sqrt (A ^ 2) + Real.sqrt (B ^ 2)) +
          Real.sqrt (F ^ 2) + Real.sqrt (H ^ 2) := by
      have h := Section6HolderInterior.sqrt_add_le_add_sqrt
        (sq_nonneg A) (sq_nonneg B)
      linarith
    _ = A + B + F + H := by
      rw [Real.sqrt_sq hA, Real.sqrt_sq hB, Real.sqrt_sq hF, Real.sqrt_sq hH]

/-- Remove the common positive coefficient after taking the square root of
the four weighted squares.  The forcing square contains the reciprocal
weight, hence it contributes `sigma⁻¹` after the exterior normalization. -/
theorem invSqrt_mul_sqrt_weighted_fourSquares_le
    {K sigma A B F H : ℝ}
    (hK : 0 ≤ K) (hsigma : 0 < sigma)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hF : 0 ≤ F) (hH : 0 ≤ H) :
    sigma ^ (-1 / 2 : ℝ) *
        Real.sqrt (K *
          ((Real.sqrt sigma * A) ^ 2 +
            (Real.sqrt sigma * B) ^ 2 +
            ((Real.sqrt sigma)⁻¹ * F) ^ 2 +
            (Real.sqrt sigma * H) ^ 2)) ≤
      Real.sqrt K * (A + B + sigma⁻¹ * F + H) := by
  have hsqrt : 0 < Real.sqrt sigma := Real.sqrt_pos.2 hsigma
  have hroot := sqrt_four_sq_le_sum
    (mul_nonneg hsqrt.le hA) (mul_nonneg hsqrt.le hB)
    (mul_nonneg (inv_nonneg.mpr hsqrt.le) hF) (mul_nonneg hsqrt.le hH)
  have hKroot : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hscaled := mul_le_mul_of_nonneg_left hroot hKroot
  have hpow : sigma ^ (-1 / 2 : ℝ) = (Real.sqrt sigma)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hsigma.le, ← Real.sqrt_eq_rpow]
  rw [hpow]
  calc
    (Real.sqrt sigma)⁻¹ * Real.sqrt
        (K * ((Real.sqrt sigma * A) ^ 2 +
          (Real.sqrt sigma * B) ^ 2 +
          ((Real.sqrt sigma)⁻¹ * F) ^ 2 +
          (Real.sqrt sigma * H) ^ 2)) =
        (Real.sqrt sigma)⁻¹ *
          (Real.sqrt K * Real.sqrt
            ((Real.sqrt sigma * A) ^ 2 +
              (Real.sqrt sigma * B) ^ 2 +
              ((Real.sqrt sigma)⁻¹ * F) ^ 2 +
              (Real.sqrt sigma * H) ^ 2)) := by rw [Real.sqrt_mul hK]
    _ ≤ (Real.sqrt sigma)⁻¹ *
        (Real.sqrt K *
          (Real.sqrt sigma * A + Real.sqrt sigma * B +
            (Real.sqrt sigma)⁻¹ * F + Real.sqrt sigma * H)) := by
      exact mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hsqrt.le)
    _ = Real.sqrt K * (A + B + sigma⁻¹ * F + H) := by
      field_simp [hsqrt.ne']
      rw [Real.sq_sqrt hsigma.le]
      ring

/-- The four weighted squares in the summed-cover estimate, converted to the
literal first-order manuscript prices. -/
theorem invSqrt_mul_sqrt_manuscriptFourBudgets_le
    {K sigma s O G F H nr : ℝ} {n : ℤ}
    (hK : 0 ≤ K) (hsigma : 0 < sigma) (hs : 0 < s)
    (hO : 0 ≤ O) (hG : 0 ≤ G) (hF : 0 ≤ F) (hH : 0 ≤ H) :
    sigma ^ (-1 / 2 : ℝ) * Real.sqrt
        (K * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 + sigma * G ^ 2 +
          s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2 +
          sigma * s ^ (-4 : ℝ) * (3 : ℝ) ^ (2 * s * nr) * H ^ 2)) ≤
      Real.sqrt K *
        ((3 : ℝ) ^ (-n) * O + G +
          sigma⁻¹ * (s ^ (-6 : ℝ) * (3 : ℝ) ^ (s * nr) * F) +
          s ^ (-2 : ℝ) * (3 : ℝ) ^ (s * nr) * H) := by
  let A := (3 : ℝ) ^ (-n) * O
  let F' := s ^ (-6 : ℝ) * (3 : ℝ) ^ (s * nr) * F
  let H' := s ^ (-2 : ℝ) * (3 : ℝ) ^ (s * nr) * H
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hF'0 : 0 ≤ F' := by dsimp [F']; positivity
  have hH'0 : 0 ≤ H' := by dsimp [H']; positivity
  have hz : ((3 : ℝ) ^ (-n)) ^ 2 = (3 : ℝ) ^ (-(2 * n)) := by
    rw [← zpow_natCast ((3 : ℝ) ^ (-n)) 2, ← zpow_mul]
    ring_nf
  have hs12 : (s ^ (-6 : ℝ)) ^ 2 = s ^ (-12 : ℝ) := by
    rw [← Real.rpow_natCast (s ^ (-6 : ℝ)) 2,
      ← Real.rpow_mul hs.le (-6) ((2 : ℕ) : ℝ)]
    norm_num
  have hs4 : (s ^ (-2 : ℝ)) ^ 2 = s ^ (-4 : ℝ) := by
    rw [← Real.rpow_natCast (s ^ (-2 : ℝ)) 2,
      ← Real.rpow_mul hs.le (-2) ((2 : ℕ) : ℝ)]
    norm_num
  have h3s : ((3 : ℝ) ^ (s * nr)) ^ 2 =
      (3 : ℝ) ^ (2 * s * nr) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (s * nr)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast
    ring_nf
  have hsig : (Real.sqrt sigma) ^ 2 = sigma := Real.sq_sqrt hsigma.le
  have hparent : sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 =
      (Real.sqrt sigma * A) ^ 2 := by
    dsimp [A]
    rw [mul_pow, mul_pow, hsig, hz]
    ring
  have haffine : sigma * G ^ 2 = (Real.sqrt sigma * G) ^ 2 := by
    rw [mul_pow, hsig]
  have hforce : s ^ (-12 : ℝ) * sigma⁻¹ *
      (3 : ℝ) ^ (2 * s * nr) * F ^ 2 =
      ((Real.sqrt sigma)⁻¹ * F') ^ 2 := by
    dsimp [F']
    rw [mul_pow, mul_pow, mul_pow, hs12, h3s, inv_pow, hsig]
    ring
  have hboundary : sigma * s ^ (-4 : ℝ) *
      (3 : ℝ) ^ (2 * s * nr) * H ^ 2 =
      (Real.sqrt sigma * H') ^ 2 := by
    dsimp [H']
    rw [mul_pow, mul_pow, mul_pow, hsig, hs4, h3s]
    ring
  rw [hparent, haffine, hforce, hboundary]
  exact invSqrt_mul_sqrt_weighted_fourSquares_le hK hsigma hA0 hG hF'0 hH'0



theorem invSqrt_mul_vectorNormalizedL2On_le_of_manuscriptFourBudgets
    {d : ℕ} (W : Set (Vec d)) (a : Vec d → ℝ) (v : Vec d → Vec d)
    {K sigma s O G F H nr : ℝ} {n : ℤ}
    (ha : ∀ x, 0 ≤ a x)
    (hK : 0 ≤ K) (hsigma : 0 < sigma) (hs : 0 < s)
    (hO : 0 ≤ O) (hG : 0 ≤ G) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (henergy : volumeAverage W (fun x ↦ a x * vecNormSq (v x)) ≤
      K * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 + sigma * G ^ 2 +
        s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2 +
        sigma * s ^ (-4 : ℝ) * (3 : ℝ) ^ (2 * s * nr) * H ^ 2)) :
    sigma ^ (-1 / 2 : ℝ) * vectorNormalizedL2On W
        (fun x ↦ Real.sqrt (a x) • v x) ≤
      Real.sqrt K *
        ((3 : ℝ) ^ (-n) * O + G +
          sigma⁻¹ * (s ^ (-6 : ℝ) * (3 : ℝ) ^ (s * nr) * F) +
          s ^ (-2 : ℝ) * (3 : ℝ) ^ (s * nr) * H) := by
  rw [Section6Holder.vectorNormalizedL2On_sqrt_smul_eq_sqrt_volumeAverage
    W a v ha]
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hscaled := mul_le_mul_of_nonneg_left hsqrt
    (Real.rpow_nonneg hsigma.le (-1 / 2 : ℝ))
  exact hscaled.trans
    (invSqrt_mul_sqrt_manuscriptFourBudgets_le hK hsigma hs hO hG hF hH)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
