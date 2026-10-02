import SubdiffusiveProcess.Section6SumErrors.ResponseMean

/-!
# RowConstants

Dimension-only coefficient bounds for the response means and Gaussian scales, and the admissible-moment consequence of the smallness budget.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
noncomputable section

/-- A dimension-only upper coefficient for the Gaussian row variance. -/
def gammaBase (d : ℕ) (C : ℝ) : ℝ := 1 + 392 * C + 512 * C * d

/-- A dimension-only upper coefficient for the squared response mean. -/
def meanBase (d : ℕ) (C : ℝ) : ℝ :=
  1 + 32 * C * (2 + 4 * d) * (4 + 4 * d)

theorem gammaBase_pos (d : ℕ) {C : ℝ} (hC : 0 < C) : 0 < gammaBase d C := by
  unfold gammaBase
  positivity

theorem meanBase_pos (d : ℕ) {C : ℝ} (hC : 0 < C) : 0 < meanBase d C := by
  unfold meanBase
  positivity

theorem inv_pow_eq_rpow (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (s ^ n)⁻¹ = s ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg hs.le, Real.rpow_natCast]

theorem gammaSqConst_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (d : ℕ) {C : ℝ} (hC : 0 < C) :
    holderResponseGammaSqConst s d C ≤ gammaBase d C / s ^ 3 := by
  have hpoly : holderResponseGammaSqConst s d C * s ^ 3 =
      s ^ 3 + 384 * C * s + 512 * C * d + 8 * C * s ^ 2 := by
    unfold holderResponseGammaSqConst holderResponseMomentFloor
      holderResponseScoreS holderResponseScoreCap
    field_simp [hs.ne']
    ring
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hs3 : s ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hs.le hs1 3
  apply (le_div_iff₀ (pow_pos hs 3)).2
  rw [hpoly]
  unfold gammaBase
  nlinarith

theorem gammaScale_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s C : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 < C) :
    holderResponseGammaScale s M C ≤
      Real.sqrt (gammaBase d C) * s ^ (-3 / 2 : ℝ) * M.delta *
        Real.sqrt |Real.log M.delta| := by
  have hb := gammaSqConst_le hs hs1 d hC
  have hsqrt : Real.sqrt (holderResponseGammaSqConst s d C) ≤
      Real.sqrt (gammaBase d C) * s ^ (-3 / 2 : ℝ) := by
    calc
      _ ≤ Real.sqrt (gammaBase d C / s ^ 3) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (gammaBase d C) * s ^ (-3 / 2 : ℝ) := by
        rw [div_eq_mul_inv, Real.sqrt_mul (gammaBase_pos d hC).le,
          inv_pow_eq_rpow s hs]
        simp only [Real.sqrt_eq_rpow]
        rw [← Real.rpow_mul hs.le]
        congr 1
        norm_num
  unfold holderResponseGammaScale
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsqrt M.shellPrefix.delta_pos.le)
    (Real.sqrt_nonneg _)

theorem rowMeanCoeff_le {s C : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (d : ℕ) (hC : 0 < C) :
    rowMeanCoeff s d C ≤ Real.sqrt (meanBase d C) * (s ^ 2)⁻¹ := by
  let q := holderResponseMomentFloor s d
  have hq : 2 ≤ q := holderResponseMomentFloor_two_le s hs d
  have hqbound : q ≤ (2 + 4 * d) / s := by
    apply (le_div_iff₀ hs).2
    have heq : q * s = 2 * s + 4 * d := by
      unfold q holderResponseMomentFloor holderResponseScoreS
      field_simp [hs.ne']
      ring
    rw [heq]
    linarith
  have hlog : Real.log (2 + q) ≤ (4 + 4 * d) / s := by
    have hl := Real.log_le_sub_one_of_pos (show 0 < 2 + q by linarith)
    have htwo : (2 : ℝ) ≤ 2 / s := by
      rw [le_div_iff₀ hs]
      linarith
    calc
      _ ≤ 2 + q := by linarith
      _ ≤ 2 / s + (2 + 4 * d) / s := add_le_add htwo hqbound
      _ = _ := by ring
  have ht : (holderResponseScoreS s ^ 2)⁻¹ = 4 / s ^ 2 := by
    unfold holderResponseScoreS
    field_simp [hs.ne']
    ring
  have hl0 : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
  have hraw0 : 0 ≤ 8 * C * (holderResponseScoreS s ^ 2)⁻¹ * q * Real.log (2 + q) := by
    have hl0 : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
    positivity
  have hraw : 8 * C * (holderResponseScoreS s ^ 2)⁻¹ * q * Real.log (2 + q) ≤
      meanBase d C / s ^ 4 := by
    rw [ht]
    calc
      _ ≤ 8 * C * (4 / s ^ 2) * ((2 + 4 * d) / s) * ((4 + 4 * d) / s) := by
        gcongr
      _ = (32 * C * (2 + 4 * d) * (4 + 4 * d)) / s ^ 4 := by ring
      _ ≤ meanBase d C / s ^ 4 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le _)
        unfold meanBase
        linarith
  have hr : 0 ≤ Real.sqrt (meanBase d C) * (s ^ 2)⁻¹ := by positivity
  unfold rowMeanCoeff
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _) hr]
  change Real.sqrt (8 * C * (holderResponseScoreS s ^ 2)⁻¹ * q * Real.log (2 + q)) ^ 2 ≤ _
  rw [Real.sq_sqrt hraw0, mul_pow, Real.sq_sqrt (meanBase_pos d hC).le]
  simpa only [inv_pow, ← pow_mul, show 2 * 2 = 4 by norm_num, div_eq_mul_inv] using hraw

theorem floor_le_cutoff {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s C K : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 < C)
    (hK : C * (2 + 4 * d) ≤ K)
    (hbudget : K * M.delta ^ 2 * |Real.log M.delta| ≤ s) :
    holderResponseMomentFloor s d ≤
      C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
  have hdelta := M.shellPrefix.delta_pos
  have hL : 0 < |Real.log M.delta| := abs_pos.mpr
    (Real.log_neg hdelta (M.shellPrefix.delta_le_half.trans_lt (by norm_num))).ne
  have hq : holderResponseMomentFloor s d * s ≤ 2 + 4 * d := by
    have heq : holderResponseMomentFloor s d * s = 2 * s + 4 * d := by
      unfold holderResponseMomentFloor holderResponseScoreS
      field_simp [hs.ne']
      ring
    rw [heq]
    linarith
  have hbud : C * (2 + 4 * d) * M.delta ^ 2 * |Real.log M.delta| ≤ s :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (sq_nonneg _)) hL.le).trans hbudget
  have hq0 : 0 ≤ holderResponseMomentFloor s d := by
    linarith [holderResponseMomentFloor_two_le s hs d]
  have hmul := mul_le_mul_of_nonneg_left hbud hq0
  have hf : holderResponseMomentFloor s d *
      (C * M.delta ^ 2 * |Real.log M.delta|) ≤ 1 := by
    apply (mul_le_mul_iff_right₀ hs).1
    nlinarith [mul_le_mul_of_nonneg_left hq (show 0 ≤ C * M.delta ^ 2 * |Real.log M.delta| by positivity)]
  have he : C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
      (C * M.delta ^ 2 * |Real.log M.delta|)⁻¹ := by simp only [mul_inv_rev]; ring
  rw [he, ← one_div]
  exact (le_div_iff₀ (by positivity)).2 hf

end
end SubdiffusiveProcess.Section6SumErrors.Response
