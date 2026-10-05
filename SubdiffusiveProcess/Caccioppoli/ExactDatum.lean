module

public import SubdiffusiveProcess.Caccioppoli.Scalar
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PositiveBesovFullDatum
@[expose] public section

namespace SubdiffusiveProcess.Caccioppoli
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal
noncomputable section
theorem entropy_and_constant_absorption
    {C₀ K s t : ℝ} (hC₀ : 0 < C₀) (hK : 1 ≤ K)
    (hs : 0 < s) (hs_one : s < 1) (ht : 0 < t) (ht_quarter : t < 1 / 2)
    (hst : s + t < 1) :
    K *
        (Real.rpow (C₀ / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
          Real.rpow s (-(2 * s / (1 - s - t)))) ≤
      Real.rpow (((Real.exp 2 * K) ^ 2 * C₀) / (1 - s - t))
        (2 + 4 * s / (1 - s - t)) := by
  let σ : ℝ := 1 - s - t
  let p : ℝ := 2 + 4 * s / σ
  let A : ℝ := Real.exp 2 * K
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσ_one : σ ≤ 1 := by dsimp [σ]; linarith
  have hp_one : 1 ≤ p := by
    dsimp [p]
    have : 0 ≤ 4 * s / σ := by positivity
    linarith
  have hp_invσ : σ⁻¹ ≤ p := by
    calc
      σ⁻¹ = 1 / σ := (one_div σ).symm
      _ ≤ p := by
        rw [div_le_iff₀ hσ]
        have hpσ : p * σ = 2 * σ + 4 * s := by
          dsimp [p]
          field_simp [hσ.ne']
        rw [hpσ]
        dsimp [σ]
        nlinarith
  have hA_one : 1 ≤ A := by
    dsimp [A]
    have : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    nlinarith
  have hK_Ap : K ≤ Real.rpow A p := by
    calc
      K ≤ A := by
        dsimp [A]
        have hexp : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
        nlinarith
      _ ≤ Real.rpow A p := Real.self_le_rpow_of_one_le hA_one hp_one
  have hentropy : Real.rpow s (-(2 * s)) ≤ Real.exp 2 :=
    rpow_neg_two_mul_self_le_exp_two hs hs_one.le
  have hfactor : Real.rpow s (-(2 * s / σ)) ≤ Real.rpow A p := by
    have hinvσ : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
    calc
      Real.rpow s (-(2 * s / σ)) =
          Real.rpow s ((-(2 * s)) * σ⁻¹) := by
        congr 1
        rw [inv_eq_one_div]
        field_simp [hσ.ne']
      _ = Real.rpow (Real.rpow s (-(2 * s))) σ⁻¹ :=
        Real.rpow_mul hs.le _ _
      _ ≤ Real.rpow (Real.exp 2) σ⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hs.le _) hentropy hinvσ
      _ ≤ Real.rpow A σ⁻¹ := by
        apply Real.rpow_le_rpow (Real.exp_pos 2).le
        · dsimp [A]
          nlinarith [Real.exp_pos 2]
        · exact hinvσ
      _ ≤ Real.rpow A p :=
        Real.rpow_le_rpow_of_exponent_le hA_one hp_invσ
  have hKF : K * Real.rpow s (-(2 * s / σ)) ≤ Real.rpow (A ^ 2) p := by
    calc
      K * Real.rpow s (-(2 * s / σ)) ≤
          Real.rpow A p * Real.rpow A p :=
        mul_le_mul hK_Ap hfactor (Real.rpow_nonneg hs.le _)
          (Real.rpow_nonneg (by linarith [hA_one]) _)
      _ = Real.rpow (A ^ 2) p := by
        rw [show A ^ 2 = A * A by ring]
        exact (Real.mul_rpow (by linarith [hA_one]) (by linarith [hA_one])).symm
  have hbase : 0 ≤ C₀ / σ := div_nonneg hC₀.le hσ.le
  calc
    K * (Real.rpow (C₀ / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
        Real.rpow s (-(2 * s / (1 - s - t)))) =
        (K * Real.rpow s (-(2 * s / σ))) * Real.rpow (C₀ / σ) p := by
      simp only [σ, p]
      ring
    _ ≤ Real.rpow (A ^ 2) p * Real.rpow (C₀ / σ) p :=
      mul_le_mul_of_nonneg_right hKF (Real.rpow_nonneg hbase _)
    _ = Real.rpow ((A ^ 2) * (C₀ / σ)) p := by
      exact (Real.mul_rpow (sq_nonneg A) hbase).symm
    _ = Real.rpow (((Real.exp 2 * K) ^ 2 * C₀) / (1 - s - t))
        (2 + 4 * s / (1 - s - t)) := by
      simp only [A, σ, p]
      congr 1
      ring


theorem positiveBesov_full_sq_le_paperNorm (d : ℕ) [NeZero d]
    {t : ℝ} (ht : 0 < t) (ht_half : t < 1 / 2)
    (sF : FractionalOrder) (hsF : sF.1 = 2 * t)
    (F : CubeEuclideanWspField (originCube d 0) sF FiniteLpExponent.two) :
    scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0) (2 * t) F.toField ^ 2 ≤
      ((d : ℝ) + caccioppoliExactDatumConstant d) ^ 2 * Real.rpow (2 * t) (-1 : ℝ) *
        (paperFractionalFullNorm (originCube d 0) sF FiniteLpExponent.two F.toField).toReal ^ 2 := by
  let S : ℝ≥0∞ := cubeEuclideanWspESeminorm (originCube d 0) sF
    FiniteLpExponent.two F.toField
  let N : ℝ≥0∞ := paperFractionalFullNorm (originCube d 0) sF
    FiniteLpExponent.two F.toField
  have hSfull := cubeEuclideanWspESeminorm_le_fullENorm
    (originCube d 0) sF FiniteLpExponent.two F.toField
  have hfullN := cubeEuclideanWspFullENorm_le_paperFractionalFullNorm
    (originCube d 0) sF FiniteLpExponent.two F.toField
  have hNtop : N ≠ ∞ := by
    dsimp [N, paperFractionalFullNorm, paperFractionalSeminorm]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
          ENNReal.ofReal_ne_top)
        F.eSeminorm_lt_top.ne
    · exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_ne_zero
          (ENNReal.ofReal_ne_zero_iff.mpr (cubeScaleFactor_pos' (originCube d 0)))
          ENNReal.ofReal_ne_top)
        F.normalizedEuclideanLpENorm_lt_top.ne
  have hfactorTop : (ENNReal.ofReal sF.1) ^
      (-(FiniteLpExponent.two.exponent.toReal)⁻¹) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr sF.2.1)
      ENNReal.ofReal_ne_top
  have hrealFull := ENNReal.toReal_mono (ENNReal.mul_ne_top hfactorTop hNtop) hfullN
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal sF.2.1.le] at hrealFull
  norm_num at hrealFull
  have hS : S.toReal ≤ Real.rpow (2 * t) (-(1 / 2 : ℝ)) * N.toReal := by
    calc
      S.toReal ≤ (cubeEuclideanWspFullENorm (originCube d 0) sF
          FiniteLpExponent.two F.toField).toReal := by
        exact ENNReal.toReal_mono F.fullENorm_lt_top.ne hSfull
      _ ≤ Real.rpow sF.1 (-(1 / 2 : ℝ)) * N.toReal := hrealFull
      _ = Real.rpow (2 * t) (-(1 / 2 : ℝ)) * N.toReal := by rw [hsF]
  let L : ℝ≥0∞ :=
    (cubeBoundedMeasurableDomain (originCube d 0)).normalizedEuclideanLpENorm
      (2 : ℝ≥0∞) F.toField
  have hLN : L ≤ N := by
    dsimp [L, N, paperFractionalFullNorm]
    have hscale : cubeScaleFactor (originCube d 0) = 1 := by
      change (3 : ℝ) ^ (0 : ℤ) = 1
      exact zpow_zero 3
    simp only [zpow_zero, ENNReal.ofReal_one, ENNReal.one_rpow, one_mul]
    exact le_add_of_nonneg_left bot_le
  have hLreal := ENNReal.toReal_mono hNtop hLN
  have hfac : 1 ≤ Real.rpow (2 * t) (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by norm_num)
  have hL : L.toReal ≤ Real.rpow (2 * t) (-(1 / 2 : ℝ)) * N.toReal :=
    hLreal.trans (by nlinarith [ENNReal.toReal_nonneg (a := N)])
  have hb := scaleNormalizedPositiveBesovVectorNormTwo_le_exactDatum_general
    (originCube d 0) sF F
  have hscale : cubeBesovScaleWeight (-sF.1) (originCube d 0) = 1 := by
    change ((3 : ℝ) ^ (0 : ℤ)) ^ (-(-sF.1)) = 1
    rw [zpow_zero, Real.one_rpow]
  rw [hscale, mul_one, hsF] at hb
  have hD : 0 ≤ caccioppoliExactDatumConstant d :=
    (caccioppoliExactDatumConstant_pos d).le
  have hb' : scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0) (2 * t) F.toField ≤
      ((d : ℝ) + caccioppoliExactDatumConstant d) *
        (Real.rpow (2 * t) (-(1 / 2 : ℝ)) * N.toReal) := by
    refine hb.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg d)
    have h2 := mul_le_mul_of_nonneg_left hS hD
    dsimp [L, S] at h1 h2
    simpa only [add_mul] using! add_le_add h1 h2
  have hnonneg : 0 ≤ scaleNormalizedPositiveBesovVectorNormTwo
      (originCube d 0) (2 * t) F.toField := by
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    apply add_nonneg (Real.sqrt_nonneg _)
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (by simpa [hsF] using! ((cubeEuclideanWspField_forceSobolevRegularity sF F).toForceBesovRegularity
        sF.2.1 sF.2.2.le))
  have hp : Real.rpow (2 * t) (-(1 / 2 : ℝ)) ^ 2 = Real.rpow (2 * t) (-1 : ℝ) := by
    calc
      _ = Real.rpow (Real.rpow (2 * t) (-(1 / 2 : ℝ))) (2 : ℝ) := (Real.rpow_two _).symm
      _ = Real.rpow (2 * t) (-(1 / 2 : ℝ) * 2) := (Real.rpow_mul (by linarith) _ _).symm
      _ = Real.rpow (2 * t) (-1 : ℝ) := by norm_num
  have hsq := pow_le_pow_left₀ hnonneg hb' 2
  simpa only [mul_pow, hp, N, mul_assoc] using! hsq

/-- One inverse regularity factor pays for the paper's Sobolev normalization. -/
theorem rpow_mul_two_t_inv_le {t k : ℝ} (ht : 0 < t) :
    Real.rpow t (-k) * Real.rpow (2 * t) (-1 : ℝ) ≤
      Real.rpow t (-(k + 1)) := by
  have h := Real.rpow_le_rpow_of_nonpos ht (by linarith : t ≤ 2 * t)
    (by norm_num : (-1 : ℝ) ≤ 0)
  calc
    _ ≤ Real.rpow t (-k) * Real.rpow t (-1 : ℝ) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ht.le _)
    _ = Real.rpow t (-k + (-1)) := (Real.rpow_add ht _ _).symm
    _ = _ := by congr 1; ring

theorem normalized_square_budget {t k M L N B : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (hB : B ≤ M * Real.rpow (2 * t) (-1 : ℝ) * N) :
    Real.rpow t (-k) * L * B ≤
      M * Real.rpow t (-(k + 1)) * L * N := by
  calc
    _ ≤ Real.rpow t (-k) * L * (M * Real.rpow (2 * t) (-1 : ℝ) * N) :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg (Real.rpow_nonneg ht.le _) hL)
    _ = (M * L * N) * (Real.rpow t (-k) * Real.rpow (2 * t) (-1 : ℝ)) := by ring
    _ ≤ (M * L * N) * Real.rpow t (-(k + 1)) :=
      mul_le_mul_of_nonneg_left (rpow_mul_two_t_inv_le ht) (mul_nonneg (mul_nonneg hM hL) hN)
    _ = _ := by ring

end
end SubdiffusiveProcess.Caccioppoli
