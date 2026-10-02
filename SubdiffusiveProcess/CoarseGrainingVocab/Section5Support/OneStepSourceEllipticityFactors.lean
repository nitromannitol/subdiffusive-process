import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceEllipticityMoments
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepTailAverageMoments




open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private noncomputable def upperTailNormalizedRoot {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ)
    (omega : Sample d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt
    ((tailCoefficientCubeAverage M (n + h) n omega)⁻¹ *
      cutoffUpperEllipticityMeasurable M (n + h) j omega))

private noncomputable def lowerTailNormalizedRoot {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ)
    (omega : Sample d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt
    (tailCoefficientCubeAverage M (n + h) n omega *
      (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹))

private theorem measurable_upperTailNormalizedRoot {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ) :
    Measurable (upperTailNormalizedRoot M n h j) := by
  exact ENNReal.continuous_ofReal.measurable.comp
    (Real.continuous_sqrt.measurable.comp
      ((measurable_tailCoefficientCubeAverage M (n + h) n).inv.mul
        (measurable_cutoffUpperEllipticityMeasurable M (n + h) j)))

private theorem measurable_lowerTailNormalizedRoot {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ) :
    Measurable (lowerTailNormalizedRoot M n h j) := by
  exact ENNReal.continuous_ofReal.measurable.comp
    (Real.continuous_sqrt.measurable.comp
      ((measurable_tailCoefficientCubeAverage M (n + h) n).mul
        (measurable_cutoffLowerEllipticityMeasurable M (n + h) j).inv))

private theorem upperTailNormalizedRoot_ae_le {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ) (hjn : j ≤ n)
    {s : ℝ} (hs : 0 < s) (hsq : s < 1 / 4) :
    upperTailNormalizedRoot M n h j ≤ᵐ[M.P.toMeasure]
      fun omega ↦ 1 + ENNReal.ofReal (Real.sqrt 2) *
        ellipticityMomentObservable M n (j : ℤ) s omega := by
  filter_upwards [cutoffUpperEllipticityMeasurable_ae_eq M (n + h) j]
    with omega heq
  rw [upperTailNormalizedRoot, heq]
  exact ofReal_sqrt_tailNormalized_highCutoffUpper_quarter_le_of_s
    M n h j hjn hs hsq omega

private theorem lowerTailNormalizedRoot_ae_le {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ) (hjn : j ≤ n)
    {s : ℝ} (hs : 0 < s) (hsq : s < 1 / 4) :
    lowerTailNormalizedRoot M n h j ≤ᵐ[M.P.toMeasure]
      fun omega ↦ 1 + ENNReal.ofReal (Real.sqrt 2) *
        ellipticityMomentObservable M n (j : ℤ) s omega := by
  filter_upwards [cutoffLowerEllipticityMeasurable_ae_eq M (n + h) j]
    with omega heq
  rw [lowerTailNormalizedRoot, heq]
  exact ofReal_sqrt_tailNormalized_highCutoffLowerInv_quarter_le_of_s
    M n h j hjn hs hsq omega

private theorem upper_root_product_sq_ae {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ) :
    (fun omega ↦
      (ENNReal.ofReal (Real.sqrt (oneStepTailCubeRatio M n h omega)) *
        upperTailNormalizedRoot M n h j omega) ^ (2 : ℕ)) =ᵐ[M.P.toMeasure]
      fun omega ↦ ENNReal.ofReal
        ((ahom M n)⁻¹ * cutoffUpperEllipticityMeasurable M (n + h) j omega) := by
  filter_upwards [cutoffUpperEllipticityMeasurable_ae_eq M (n + h) j]
    with omega heq
  have ht : 0 < tailCoefficientCubeAverage M (n + h) n omega :=
    tailCoefficientCubeAverage_pos M (n + h) n omega
  have hh : 0 < ahom M n := ahom_pos M n
  have hu : 0 ≤ cutoffUpperEllipticityMeasurable M (n + h) j omega := by
    rw [heq]
    exact Ch04.LambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num)
  have hXsq : ENNReal.ofReal (Real.sqrt (oneStepTailCubeRatio M n h omega)) ^
      (2 : ℕ) = ENNReal.ofReal (oneStepTailCubeRatio M n h omega) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (oneStepTailCubeRatio_pos M n h omega).le]
  have hYsq : upperTailNormalizedRoot M n h j omega ^ (2 : ℕ) =
      ENNReal.ofReal ((tailCoefficientCubeAverage M (n + h) n omega)⁻¹ *
        cutoffUpperEllipticityMeasurable M (n + h) j omega) := by
    unfold upperTailNormalizedRoot
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr ht.le) hu)]
  rw [mul_pow, hXsq, hYsq,
    ← ENNReal.ofReal_mul (oneStepTailCubeRatio_pos M n h omega).le]
  apply congrArg ENNReal.ofReal
  unfold oneStepTailCubeRatio
  field_simp [ht.ne', hh.ne']

private theorem lower_root_product_sq_ae {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ) :
    (fun omega ↦
      (ENNReal.ofReal (Real.sqrt (oneStepTailCubeInvRatio M n h omega)) *
        lowerTailNormalizedRoot M n h j omega) ^ (2 : ℕ)) =ᵐ[M.P.toMeasure]
      fun omega ↦ ENNReal.ofReal
        (ahom M n * (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹) := by
  filter_upwards [cutoffLowerEllipticityMeasurable_ae_eq M (n + h) j]
    with omega heq
  have ht : 0 < tailCoefficientCubeAverage M (n + h) n omega :=
    tailCoefficientCubeAverage_pos M (n + h) n omega
  have hh : 0 < ahom M n := ahom_pos M n
  have hl : 0 < cutoffLowerEllipticityMeasurable M (n + h) j omega := by
    rw [heq]
    let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField
      M (n + h) omega
    unfold Ch04.lambdaSqCoeffField
    rw [dif_pos hlocal]
    exact Ch02.lambdaSq_finite_pos _ _ (by norm_num) (by norm_num)
  have hXsq : ENNReal.ofReal (Real.sqrt (oneStepTailCubeInvRatio M n h omega)) ^
      (2 : ℕ) = ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (oneStepTailCubeInvRatio_pos M n h omega).le]
  have hYsq : lowerTailNormalizedRoot M n h j omega ^ (2 : ℕ) =
      ENNReal.ofReal (tailCoefficientCubeAverage M (n + h) n omega *
        (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹) := by
    unfold lowerTailNormalizedRoot
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg ht.le (inv_nonneg.mpr hl.le))]
  rw [mul_pow, hXsq, hYsq,
    ← ENNReal.ofReal_mul (oneStepTailCubeInvRatio_pos M n h omega).le]
  apply congrArg ENNReal.ofReal
  unfold oneStepTailCubeInvRatio
  field_simp [ht.ne', hh.ne', hl.ne']

/-- Abstract upper Holder fold. -/
theorem paperENNRealLpNorm_sourceCell_upper_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ) (hjn : j ≤ n)
    {s R T : ℝ} (hs : 0 < s) (hsq : s < 1 / 4)
    (hR : 0 ≤ R)
    (herror : paperENNRealLpNorm M.P.toMeasure 8
      (ellipticityMomentObservable M n (j : ℤ) s) ≤ ENNReal.ofReal R)
    (hT : 0 ≤ T)
    (htail : paperENNRealLpNorm M.P.toMeasure 8
      (fun omega ↦ ENNReal.ofReal (oneStepTailCubeRatio M n h omega)) ≤
        ENNReal.ofReal T) :
    paperENNRealLpNorm M.P.toMeasure 2
        (fun omega ↦ ENNReal.ofReal
          (cutoffUpperEllipticityMeasurable M (n + h) j omega)) ≤
      ENNReal.ofReal (ahom M n *
        (Real.sqrt T * (1 + Real.sqrt 2 * R)) ^ 2) := by
  let X : Sample d → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (Real.sqrt (oneStepTailCubeRatio M n h omega))
  let Y : Sample d → ℝ≥0∞ := upperTailNormalizedRoot M n h j
  have hXm : Measurable X := ENNReal.continuous_ofReal.measurable.comp
    (Real.continuous_sqrt.measurable.comp (measurable_oneStepTailCubeRatio M n h))
  have hYm : Measurable Y := measurable_upperTailNormalizedRoot M n h j
  have hXeq : X = fun omega ↦
      (ENNReal.ofReal (oneStepTailCubeRatio M n h omega)) ^ (1 / 2 : ℝ) := by
    funext omega
    dsimp only [X]
    rw [Real.sqrt_eq_rpow,
      ENNReal.ofReal_rpow_of_nonneg
        (oneStepTailCubeRatio_pos M n h omega).le (by norm_num)]
  have hX8 : paperENNRealLpNorm M.P.toMeasure 8 X ≤
      ENNReal.ofReal (Real.sqrt T) := by
    rw [hXeq]
    refine (paperENNRealLpNorm_rpow_half_le M.P.toMeasure (p := 8) (by norm_num)
      (X := fun omega ↦ ENNReal.ofReal (oneStepTailCubeRatio M n h omega))
      ((ENNReal.continuous_ofReal.measurable.comp
        (measurable_oneStepTailCubeRatio M n h)))).trans ?_
    calc
      (paperENNRealLpNorm M.P.toMeasure 8 (fun omega ↦
          ENNReal.ofReal (oneStepTailCubeRatio M n h omega))) ^ (1 / 2 : ℝ) ≤
        (ENNReal.ofReal T) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow htail (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt T) := by
        rw [Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg hT (by norm_num)]
  have hY8 : paperENNRealLpNorm M.P.toMeasure 8 Y ≤
      ENNReal.ofReal (1 + Real.sqrt 2 * R) := by
    have hrawUpper : paperENNRealLpNorm M.P.toMeasure 8 Y ≤
        paperENNRealLpNorm M.P.toMeasure 8 (fun omega ↦
          1 + ENNReal.ofReal (Real.sqrt 2) *
            ellipticityMomentObservable M n (j : ℤ) s omega) :=
      paperENNRealLpNorm_mono_ae M.P.toMeasure (xi := 8) (by norm_num)
        (upperTailNormalizedRoot_ae_le M n h j hjn hs hsq)
    have hadd := paperENNRealLpNorm_le_one_add_const_mul_of_pointwise
      M.P.toMeasure (by norm_num : (1 : ℝ) ≤ 8)
      (ENNReal.ofReal (Real.sqrt 2))
      (measurable_ellipticityMomentObservable M n (j : ℤ) s)
      (fun omega ↦ le_rfl)
    refine hrawUpper.trans (hadd.trans ?_)
    calc
      1 + ENNReal.ofReal (Real.sqrt 2) *
          paperENNRealLpNorm M.P.toMeasure 8
            (ellipticityMomentObservable M n (j : ℤ) s) ≤
        1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal R := by
          gcongr
      _ = ENNReal.ofReal (1 + Real.sqrt 2 * R) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2),
          ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num)
            (mul_nonneg (Real.sqrt_nonneg 2) hR)]
  have hprod := paperENNRealLpNorm_mul_le_two_mul M.P.toMeasure
    (by norm_num : (0 : ℝ) < 4) hXm.aemeasurable hYm.aemeasurable
  have hprodBound : paperENNRealLpNorm M.P.toMeasure 4
      (fun omega ↦ X omega * Y omega) ≤
        ENNReal.ofReal (Real.sqrt T * (1 + Real.sqrt 2 * R)) := by
    norm_num at hprod
    refine hprod.trans ?_
    calc
      paperENNRealLpNorm M.P.toMeasure 8 X *
          paperENNRealLpNorm M.P.toMeasure 8 Y ≤
        ENNReal.ofReal (Real.sqrt T) * ENNReal.ofReal (1 + Real.sqrt 2 * R) :=
          mul_le_mul' hX8 hY8
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg T)]
  have hratio : paperENNRealLpNorm M.P.toMeasure 2
      (fun omega ↦ ENNReal.ofReal ((ahom M n)⁻¹ *
        cutoffUpperEllipticityMeasurable M (n + h) j omega)) ≤
      ENNReal.ofReal ((Real.sqrt T * (1 + Real.sqrt 2 * R)) ^ 2) := by
    rw [paperENNRealLpNorm_congr_ae M.P.toMeasure 2
      (upper_root_product_sq_ae M n h j).symm,
      paperENNRealLpNorm_sq M.P.toMeasure (by norm_num)]
    norm_num
    have hp := pow_le_pow_left' hprodBound 2
    let A : ℝ := Real.sqrt T * (1 + Real.sqrt 2 * R)
    have hA : 0 ≤ A := by
      dsimp only [A]
      positivity
    have hp' : (paperENNRealLpNorm M.P.toMeasure 4
        (fun omega ↦ X omega * Y omega)) ^ (2 : ℕ) ≤
        ENNReal.ofReal A ^ (2 : ℕ) := by
      simpa only [A] using hp
    exact hp'.trans_eq (ENNReal.ofReal_pow hA 2).symm
  have hscale : (fun omega ↦ ENNReal.ofReal
      (cutoffUpperEllipticityMeasurable M (n + h) j omega)) =ᵐ[M.P.toMeasure]
      fun omega ↦ ENNReal.ofReal (ahom M n) *
        ENNReal.ofReal ((ahom M n)⁻¹ *
          cutoffUpperEllipticityMeasurable M (n + h) j omega) := by
    filter_upwards [cutoffUpperEllipticityMeasurable_ae_eq M (n + h) j]
      with omega heq
    have hh := ahom_pos M n
    have hu : 0 ≤ cutoffUpperEllipticityMeasurable M (n + h) j omega := by
      rw [heq]
      exact Ch04.LambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num)
    rw [← ENNReal.ofReal_mul hh.le]
    congr 1
    field_simp [hh.ne']
  rw [paperENNRealLpNorm_congr_ae M.P.toMeasure 2 hscale]
  let Z : Sample d → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal ((ahom M n)⁻¹ *
      cutoffUpperEllipticityMeasurable M (n + h) j omega)
  have hZm : Measurable Z := ENNReal.continuous_ofReal.measurable.comp
    (measurable_const.mul
      (measurable_cutoffUpperEllipticityMeasurable M (n + h) j))
  change paperENNRealLpNorm M.P.toMeasure 2
      (fun omega ↦ ENNReal.ofReal (ahom M n) * Z omega) ≤ _
  rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure (by norm_num)
    (ENNReal.ofReal (ahom M n)) Z hZm]
  calc
    ENNReal.ofReal (ahom M n) *
        paperENNRealLpNorm M.P.toMeasure 2 (fun omega ↦
          ENNReal.ofReal ((ahom M n)⁻¹ *
            cutoffUpperEllipticityMeasurable M (n + h) j omega)) ≤
      ENNReal.ofReal (ahom M n) *
        ENNReal.ofReal ((Real.sqrt T * (1 + Real.sqrt 2 * R)) ^ 2) :=
      mul_le_mul' le_rfl hratio
    _ = ENNReal.ofReal (ahom M n *
        (Real.sqrt T * (1 + Real.sqrt 2 * R)) ^ 2) := by
      rw [← ENNReal.ofReal_mul (ahom_pos M n).le]

/-- Abstract inverse-lower Holder fold. -/
theorem paperENNRealLpNorm_sourceCell_lowerInv_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h j : ℕ) (hjn : j ≤ n)
    {s R T : ℝ} (hs : 0 < s) (hsq : s < 1 / 4)
    (hR : 0 ≤ R)
    (herror : paperENNRealLpNorm M.P.toMeasure 8
      (ellipticityMomentObservable M n (j : ℤ) s) ≤ ENNReal.ofReal R)
    (hT : 0 ≤ T)
    (htail : paperENNRealLpNorm M.P.toMeasure 8
      (fun omega ↦ ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega)) ≤
        ENNReal.ofReal T) :
    paperENNRealLpNorm M.P.toMeasure 2
        (fun omega ↦ ENNReal.ofReal
          ((cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹)) ≤
      ENNReal.ofReal ((ahom M n)⁻¹ *
        (Real.sqrt T * (1 + Real.sqrt 2 * R)) ^ 2) := by
  let X : Sample d → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (Real.sqrt (oneStepTailCubeInvRatio M n h omega))
  let Y : Sample d → ℝ≥0∞ := lowerTailNormalizedRoot M n h j
  have hXm : Measurable X := ENNReal.continuous_ofReal.measurable.comp
    (Real.continuous_sqrt.measurable.comp
      (measurable_oneStepTailCubeInvRatio M n h))
  have hYm : Measurable Y := measurable_lowerTailNormalizedRoot M n h j
  have hXeq : X = fun omega ↦
      (ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega)) ^ (1 / 2 : ℝ) := by
    funext omega
    dsimp only [X]
    rw [Real.sqrt_eq_rpow,
      ENNReal.ofReal_rpow_of_nonneg
        (oneStepTailCubeInvRatio_pos M n h omega).le (by norm_num)]
  have hX8 : paperENNRealLpNorm M.P.toMeasure 8 X ≤
      ENNReal.ofReal (Real.sqrt T) := by
    rw [hXeq]
    refine (paperENNRealLpNorm_rpow_half_le M.P.toMeasure (p := 8) (by norm_num)
      (X := fun omega ↦ ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega))
      ((ENNReal.continuous_ofReal.measurable.comp
        (measurable_oneStepTailCubeInvRatio M n h)))).trans ?_
    calc
      (paperENNRealLpNorm M.P.toMeasure 8 (fun omega ↦
          ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega))) ^ (1 / 2 : ℝ) ≤
        (ENNReal.ofReal T) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow htail (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt T) := by
        rw [Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg hT (by norm_num)]
  have hY8 : paperENNRealLpNorm M.P.toMeasure 8 Y ≤
      ENNReal.ofReal (1 + Real.sqrt 2 * R) := by
    have hraw : paperENNRealLpNorm M.P.toMeasure 8 Y ≤
        paperENNRealLpNorm M.P.toMeasure 8 (fun omega ↦
          1 + ENNReal.ofReal (Real.sqrt 2) *
            ellipticityMomentObservable M n (j : ℤ) s omega) :=
      paperENNRealLpNorm_mono_ae M.P.toMeasure (xi := 8) (by norm_num)
        (lowerTailNormalizedRoot_ae_le M n h j hjn hs hsq)
    have hadd := paperENNRealLpNorm_le_one_add_const_mul_of_pointwise
      M.P.toMeasure (by norm_num : (1 : ℝ) ≤ 8)
      (ENNReal.ofReal (Real.sqrt 2))
      (measurable_ellipticityMomentObservable M n (j : ℤ) s)
      (fun omega ↦ le_rfl)
    refine hraw.trans (hadd.trans ?_)
    calc
      1 + ENNReal.ofReal (Real.sqrt 2) *
          paperENNRealLpNorm M.P.toMeasure 8
            (ellipticityMomentObservable M n (j : ℤ) s) ≤
        1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal R := by
          gcongr
      _ = ENNReal.ofReal (1 + Real.sqrt 2 * R) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2),
          ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num)
            (mul_nonneg (Real.sqrt_nonneg 2) hR)]
  have hprod := paperENNRealLpNorm_mul_le_two_mul M.P.toMeasure
    (by norm_num : (0 : ℝ) < 4) hXm.aemeasurable hYm.aemeasurable
  norm_num at hprod
  have hprodBound : paperENNRealLpNorm M.P.toMeasure 4
      (fun omega ↦ X omega * Y omega) ≤
        ENNReal.ofReal (Real.sqrt T * (1 + Real.sqrt 2 * R)) := by
    refine hprod.trans ?_
    calc
      paperENNRealLpNorm M.P.toMeasure 8 X *
          paperENNRealLpNorm M.P.toMeasure 8 Y ≤
        ENNReal.ofReal (Real.sqrt T) * ENNReal.ofReal (1 + Real.sqrt 2 * R) :=
          mul_le_mul' hX8 hY8
      _ = _ := by rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg T)]
  have hratio : paperENNRealLpNorm M.P.toMeasure 2
      (fun omega ↦ ENNReal.ofReal (ahom M n *
        (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹)) ≤
      ENNReal.ofReal ((Real.sqrt T * (1 + Real.sqrt 2 * R)) ^ 2) := by
    rw [paperENNRealLpNorm_congr_ae M.P.toMeasure 2
      (lower_root_product_sq_ae M n h j).symm,
      paperENNRealLpNorm_sq M.P.toMeasure (by norm_num)]
    norm_num
    have hp := pow_le_pow_left' hprodBound 2
    let A : ℝ := Real.sqrt T * (1 + Real.sqrt 2 * R)
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    have hp' : (paperENNRealLpNorm M.P.toMeasure 4
        (fun omega ↦ X omega * Y omega)) ^ (2 : ℕ) ≤
        ENNReal.ofReal A ^ (2 : ℕ) := by simpa only [A] using hp
    exact hp'.trans_eq (ENNReal.ofReal_pow hA 2).symm
  have hscale : (fun omega ↦ ENNReal.ofReal
      ((cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹)) =ᵐ[M.P.toMeasure]
      fun omega ↦ ENNReal.ofReal ((ahom M n)⁻¹) *
        ENNReal.ofReal (ahom M n *
          (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹) := by
    filter_upwards [cutoffLowerEllipticityMeasurable_ae_eq M (n + h) j]
      with omega heq
    have hh := ahom_pos M n
    have hl : 0 < cutoffLowerEllipticityMeasurable M (n + h) j omega := by
      rw [heq]
      let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField
        M (n + h) omega
      unfold Ch04.lambdaSqCoeffField
      rw [dif_pos hlocal]
      exact Ch02.lambdaSq_finite_pos _ _ (by norm_num) (by norm_num)
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hh.le)]
    congr 1
    field_simp [hh.ne', hl.ne']
  rw [paperENNRealLpNorm_congr_ae M.P.toMeasure 2 hscale]
  let Z : Sample d → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (ahom M n *
      (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹)
  have hZm : Measurable Z := ENNReal.continuous_ofReal.measurable.comp
    (measurable_const.mul
      (measurable_cutoffLowerEllipticityMeasurable M (n + h) j).inv)
  change paperENNRealLpNorm M.P.toMeasure 2
      (fun omega ↦ ENNReal.ofReal ((ahom M n)⁻¹) * Z omega) ≤ _
  rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure (by norm_num)
    (ENNReal.ofReal ((ahom M n)⁻¹)) Z hZm]
  calc
    ENNReal.ofReal ((ahom M n)⁻¹) *
        paperENNRealLpNorm M.P.toMeasure 2 (fun omega ↦
          ENNReal.ofReal (ahom M n *
            (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹)) ≤
      ENNReal.ofReal ((ahom M n)⁻¹) *
        ENNReal.ofReal ((Real.sqrt T * (1 + Real.sqrt 2 * R)) ^ 2) :=
      mul_le_mul' le_rfl hratio
    _ = ENNReal.ofReal ((ahom M n)⁻¹ *
        (Real.sqrt T * (1 + Real.sqrt 2 * R)) ^ 2) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (ahom_pos M n).le)]

/-- Concrete source-scale second moments for the two coefficient factors in
the Dirichlet and Neumann cell arguments.  The small-disorder threshold is
the one supplied by the closed Section 4 recursion; the block suffix is
uniform for every `h ≤ delta⁻¹`. -/
theorem exists_sourceScale_highCutoff_ellipticity_moments
    {d : ℕ} [NeZero d] :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ (n h : ℕ), (h : ℝ) ≤ M.delta⁻¹ →
          oneStepLocalizationDepth M.delta ≤ n →
          let j := oneStepLocalizationScale n M.delta
          Integrable (fun omega : Sample d ↦
            cutoffUpperEllipticityMeasurable M (n + h) j omega ^ (2 : ℕ))
              M.P.toMeasure ∧
          (∫ omega : Sample d,
              cutoffUpperEllipticityMeasurable M (n + h) j omega ^ (2 : ℕ)
                ∂M.P.toMeasure) ≤ (C * ahom M n) ^ (2 : ℕ) ∧
          Integrable (fun omega : Sample d ↦
            (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹ ^ (2 : ℕ))
              M.P.toMeasure ∧
          (∫ omega : Sample d,
              (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹ ^ (2 : ℕ)
                ∂M.P.toMeasure) ≤ (C * (ahom M n)⁻¹) ^ (2 : ℕ) := by
  obtain ⟨delta0, R, hdelta0, hR, hsource⟩ :=
    exists_sourceScale_ellipticityMoment_bound (d := d)
  let T : ℝ := oneStepTailMomentConst
  let C : ℝ := (Real.sqrt T * (1 + Real.sqrt 2 * R)) ^ 2
  have hT : 0 < T := by exact oneStepTailMomentConst_pos
  have hC : 0 < C := by
    dsimp only [C]
    have hroot : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
    have hsum : 0 < 1 + Real.sqrt 2 * R := by positivity
    positivity
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM n h hblock hdepth
  let j := oneStepLocalizationScale n M.delta
  have hjn : j ≤ n := by
    dsimp only [j, oneStepLocalizationScale]
    exact Nat.sub_le _ _
  have hhigh := hsource M hM n hdepth
  have herror8 : paperENNRealLpNorm M.P.toMeasure 8
      (ellipticityMomentObservable M n (j : ℤ) sourceEllipticityWeight) ≤
        ENNReal.ofReal R := by
    exact (paperENNRealLpNorm_le_of_exponent_le M.P.toMeasure
      (by norm_num : (0 : ℝ) < 8)
      (by have := sourceEllipticityExponent_large d; linarith)
      (measurable_ellipticityMomentObservable M n (j : ℤ)
        sourceEllipticityWeight)).trans hhigh
  have hupperNorm := paperENNRealLpNorm_sourceCell_upper_le
    M n h j hjn sourceEllipticityWeight_pos
    (by norm_num [sourceEllipticityWeight]) hR.le herror8 hT.le
    (paperENNRealLpNorm_oneStepTailCubeRatio_eight_le M n h hblock)
  have hlowerNorm := paperENNRealLpNorm_sourceCell_lowerInv_le
    M n h j hjn sourceEllipticityWeight_pos
    (by norm_num [sourceEllipticityWeight]) hR.le herror8 hT.le
    (paperENNRealLpNorm_oneStepTailCubeInvRatio_eight_le M n h hblock)
  have hupperMeas :=
    measurable_cutoffUpperEllipticityMeasurable M (n + h) j
  have hlowerMeas :=
    (measurable_cutoffLowerEllipticityMeasurable M (n + h) j).inv
  have hupperNonneg : ∀ᵐ omega ∂M.P.toMeasure,
      0 ≤ cutoffUpperEllipticityMeasurable M (n + h) j omega := by
    filter_upwards [cutoffUpperEllipticityMeasurable_ae_eq M (n + h) j]
      with omega heq
    rw [heq]
    exact Ch04.LambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num)
  have hlowerNonneg : ∀ᵐ omega ∂M.P.toMeasure,
      0 ≤ (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹ := by
    filter_upwards [cutoffLowerEllipticityMeasurable_ae_eq M (n + h) j]
      with omega heq
    rw [heq]
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num))
  have hupperL : 0 ≤ ahom M n * C :=
    mul_nonneg (ahom_pos M n).le hC.le
  have hlowerL : 0 ≤ (ahom M n)⁻¹ * C :=
    mul_nonneg (inv_nonneg.mpr (ahom_pos M n).le) hC.le
  have hupperNorm' : paperENNRealLpNorm M.P.toMeasure 2
      (fun omega ↦ ENNReal.ofReal
        (cutoffUpperEllipticityMeasurable M (n + h) j omega)) ≤
        ENNReal.ofReal (ahom M n * C) := by
    simpa only [C, T] using hupperNorm
  have hlowerNorm' : paperENNRealLpNorm M.P.toMeasure 2
      (fun omega ↦ ENNReal.ofReal
        ((cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹)) ≤
        ENNReal.ofReal ((ahom M n)⁻¹ * C) := by
    simpa only [C, T] using hlowerNorm
  obtain ⟨hupperInt, hupperBound⟩ :=
    integrable_sq_and_integral_sq_le_of_paperENNRealLpNorm_two_of_ae_nonneg
      M.P.toMeasure hupperMeas hupperNonneg hupperL hupperNorm'
  obtain ⟨hlowerInt, hlowerBound⟩ :=
    integrable_sq_and_integral_sq_le_of_paperENNRealLpNorm_two_of_ae_nonneg
      M.P.toMeasure hlowerMeas hlowerNonneg hlowerL hlowerNorm'
  dsimp only [j]
  refine ⟨hupperInt, ?_, hlowerInt, ?_⟩
  · simpa [mul_comm] using hupperBound
  · simpa [mul_comm] using hlowerBound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
