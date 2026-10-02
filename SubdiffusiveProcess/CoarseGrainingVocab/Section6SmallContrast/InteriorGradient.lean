import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.GradientScaleReadout

/-!
# Uniform interior gradient Morrey row
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-- The dimension-only gradient-row constant delivered by the printed proof. -/
def smallContrastGradientConstant (d : ℕ) : ℝ :=
  16 * ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 *
    smallContrastUnitBallVolumePrice d

theorem smallContrastGradientConstant_nonneg (d : ℕ) :
    0 ≤ smallContrastGradientConstant d := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _))
    (smallContrastUnitBallVolumePrice_nonneg d)

/-- The local Morrey-gradient row used by Poincare and Campanato. -/
def HasInteriorSmallContrastGradientScaleBound
    (alpha K : ℝ) (u : H1Function (smallContrastUnitBall d)) : Prop :=
  ∀ z ∈ smallContrastBall d (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
    r ^ (1 - alpha) *
      vectorNormalizedL2On (euclideanBall z r) u.grad ≤ K

private theorem euclideanNorm_lt_half_of_mem_halfBall [NeZero d]
    {z : Vec d} (hz : z ∈ smallContrastBall d (1 / 2)) :
    euclideanNorm z < 1 / 2 := by
  have hzE := (mem_euclideanBall_toEuc_iff z 0
    (by norm_num : (0 : ℝ) < 1 / 2)).2 hz
  have hzE' : ‖toEuc z‖ < (1 / 2 : ℝ) := by
    simpa only [Metric.mem_ball, map_zero, dist_zero_right] using hzE
  unfold euclideanNorm
  have hsq := norm_sq_toEuc_sub z 0
  simp only [map_zero, sub_zero, euclideanSqDist] at hsq
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  exact hzE'

private theorem halfBall_subset_unitBall [NeZero d]
    {z : Vec d} (hz : z ∈ smallContrastBall d (1 / 2)) :
    euclideanBall z (1 / 2) ⊆ smallContrastUnitBall d := by
  apply euclideanBall_subset_of_center_distance_add_lt
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hzhalf := euclideanNorm_lt_half_of_mem_halfBall hz
  simpa only [sub_zero] using (show euclideanNorm z + 1 / 2 ≤ 1 by linarith)

private theorem sqrt_volume_unit_div_halfBall [NeZero d] (z : Vec d) :
    Real.sqrt ((volume (smallContrastUnitBall d)).toReal /
        (volume (euclideanBall z (1 / 2))).toReal) =
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := by
  have hhalf := volume_euclideanBall_toReal_eq_unit_mul_pow
    (d := d) z (by norm_num : (0 : ℝ) < 1 / 2)
  rw [hhalf]
  have hV : 0 < (volume (smallContrastUnitBall d)).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero
        (0 : Vec d) (by norm_num)))
  rw [show (volume (smallContrastUnitBall d)).toReal /
      ((volume (smallContrastUnitBall d)).toReal * (1 / 2 : ℝ) ^ d) =
      1 / ((1 / 2 : ℝ) ^ d) by field_simp]
  rw [show 1 / ((1 / 2 : ℝ) ^ d) = (2 : ℝ) ^ d by
    rw [div_pow]
    norm_num]
  rw [show Real.sqrt ((2 : ℝ) ^ d) = (2 : ℝ) ^ ((d : ℝ) / 2) by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring]
  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg_eq_inv_rpow]
  norm_num

/-- D-054 gradient conclusion, uniformly at every centre of `B_{1/2}`. -/
theorem interiorGradientScaleBound_of_smallContrast [NeZero d]
    {a : CoeffField d} {u : H1Function (smallContrastUnitBall d)}
    {f : Vec d → Vec d} {lam Lam delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hEll : IsEllipticFieldOn lam Lam (smallContrastUnitBall d) a)
    (ha : CoefficientIdentityDistanceLE (smallContrastUnitBall d) a delta)
    (hu : IsMatrixDivFormWeakSolutionOn a (smallContrastUnitBall d) u f)
    (hf : MemVectorLpOn (smallContrastUnitBall d)
      (schauderSourceExponent d alpha) f) :
    HasInteriorSmallContrastGradientScaleBound alpha
      (smallContrastGradientConstant d * smallContrastDataSize d alpha u f) u := by
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha.1
  have hgradUnit : MemVectorL2 (smallContrastUnitBall d) u.grad :=
    u.grad_memVectorL2
  have hgradNorm :
      vectorNormalizedL2On (smallContrastUnitBall d) u.grad ≤
        smallContrastUnitBallVolumePrice d *
          vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad := by
    simpa only [smallContrastUnitBall, one_mul, mul_one, Real.one_rpow] using
      (vectorNormalizedL2On_euclideanBall_le_price_mul_rpow_mul_globalLp
        (d := d) (U := smallContrastUnitBall d) (0 : Vec d)
        (r := 1) (p := 2) (f := u.grad) (by norm_num) (by norm_num)
        (Set.Subset.rfl) (by
          change MemLp (fun x => HilbertVec.ofVec (u.grad x))
            (ENNReal.ofReal 2) (volume.restrict (smallContrastUnitBall d))
          simpa only [ENNReal.ofReal_ofNat] using
            (memHilbertVectorL2_hilbertifyVecField hgradUnit)))
  intro z hz r hr hrhalf
  have houter := halfBall_subset_unitBall hz
  have hdyadic := dyadicGradientScaleBound_on_interiorBall
    (d := d) z (R := 1 / 2) (by norm_num) houter hd halpha0 halpha.2
      hdelta0 hdelta (isOpen_euclideanBall 0 (1 : ℝ)) hEll ha hu hf
  have hgradHalf : MemVectorL2 (euclideanBall z (1 / 2)) u.grad :=
    hgradUnit.mono_measure (Measure.restrict_mono houter le_rfl)
  have hread := gradientScaleBound_of_dyadic (d := d) z
    (R := 1 / 2) (alpha := alpha) (by norm_num) halpha.2 hgradHalf hdyadic r hr hrhalf
  have hhalfNorm := vectorNormalizedL2On_le_of_subset houter
    (by
      exact lt_of_le_of_ne ENNReal.toReal_nonneg
        (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero
          (0 : Vec d) (by norm_num))))
    (by
      exact lt_of_le_of_ne ENNReal.toReal_nonneg
        (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero
          z (by norm_num))))
    (memHilbertVectorL2_hilbertifyVecField hgradUnit)
  rw [sqrt_volume_unit_div_halfBall z] at hhalfNorm
  have hRpow : (1 / 2 : ℝ) ^ (1 - alpha) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (sub_nonneg.mpr halpha.2.le)
  have hK :
      (1 / 2 : ℝ) ^ (1 - alpha) *
            vectorNormalizedL2On (euclideanBall z (1 / 2)) u.grad +
          16 * (1 - alpha)⁻¹ *
            ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
              smallContrastUnitBallVolumePrice d) *
            vectorLpSizeOn (smallContrastUnitBall d)
              (schauderSourceExponent d alpha) f ≤
        16 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          smallContrastUnitBallVolumePrice d * smallContrastDataSize d alpha u f := by
    have hfirst := mul_le_mul hRpow hhalfNorm (Real.sqrt_nonneg _) zero_le_one
    have hfirstClean :
        (1 / 2 : ℝ) ^ (1 - alpha) *
            vectorNormalizedL2On (euclideanBall z (1 / 2)) u.grad ≤
          (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
            vectorNormalizedL2On (smallContrastUnitBall d) u.grad := by
      simpa only [one_mul] using hfirst
    have hhalfPow : 0 ≤ (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hprice : 0 ≤ smallContrastUnitBallVolumePrice d :=
      smallContrastUnitBallVolumePrice_nonneg d
    let G : ℝ := vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad
    let F : ℝ := vectorLpSizeOn (smallContrastUnitBall d)
      (schauderSourceExponent d alpha) f
    let C0 : ℝ := (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
      smallContrastUnitBallVolumePrice d
    have hgradData : 0 ≤ G :=
      ENNReal.toReal_nonneg
    have hC0 : 0 ≤ C0 := mul_nonneg hhalfPow hprice
    have hfirst' :
        (1 / 2 : ℝ) ^ (1 - alpha) *
            vectorNormalizedL2On (euclideanBall z (1 / 2)) u.grad ≤ C0 * G := by
      exact hfirstClean.trans (by
        dsimp only [C0, G]
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hgradNorm hhalfPow))
    have hgradEnlarge : C0 * G ≤ 16 * C0 * G := by
      nlinarith [mul_nonneg hC0 hgradData]
    dsimp only [smallContrastDataSize]
    calc
      (1 / 2 : ℝ) ^ (1 - alpha) *
            vectorNormalizedL2On (euclideanBall z (1 / 2)) u.grad +
          16 * (1 - alpha)⁻¹ *
            ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
              smallContrastUnitBallVolumePrice d) *
            vectorLpSizeOn (smallContrastUnitBall d)
              (schauderSourceExponent d alpha) f
          ≤ C0 * G +
            16 * (1 - alpha)⁻¹ *
              C0 * F := by
        dsimp only [C0, G, F]
        exact add_le_add hfirst' le_rfl
      _ ≤ 16 * C0 * G + 16 * (1 - alpha)⁻¹ * C0 * F :=
        add_le_add hgradEnlarge le_rfl
      _ = 16 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          smallContrastUnitBallVolumePrice d *
            (vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad +
              (1 - alpha)⁻¹ * vectorLpSizeOn (smallContrastUnitBall d)
                (schauderSourceExponent d alpha) f) := by
        dsimp only [C0, G, F]
        ring
  calc
    r ^ (1 - alpha) * vectorNormalizedL2On (euclideanBall z r) u.grad ≤
        (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          ((1 / 2 : ℝ) ^ (1 - alpha) *
              vectorNormalizedL2On (euclideanBall z (1 / 2)) u.grad +
            16 * (1 - alpha)⁻¹ *
              ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
                smallContrastUnitBallVolumePrice d) *
              vectorLpSizeOn (smallContrastUnitBall d)
                (schauderSourceExponent d alpha) f) := hread
    _ ≤ (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          (16 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
            smallContrastUnitBallVolumePrice d * smallContrastDataSize d alpha u f) :=
      mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg (by norm_num) _)
    _ = smallContrastGradientConstant d * smallContrastDataSize d alpha u f := by
      rw [smallContrastGradientConstant]
      ring

/-- The first row of the final proposition, at the source's concentric balls. -/
theorem gradientScaleBound_of_smallContrast [NeZero d]
    {a : CoeffField d} {u : H1Function (smallContrastUnitBall d)}
    {f : Vec d → Vec d} {lam Lam delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hEll : IsEllipticFieldOn lam Lam (smallContrastUnitBall d) a)
    (ha : CoefficientIdentityDistanceLE (smallContrastUnitBall d) a delta)
    (hu : IsMatrixDivFormWeakSolutionOn a (smallContrastUnitBall d) u f)
    (hf : MemVectorLpOn (smallContrastUnitBall d)
      (schauderSourceExponent d alpha) f) :
    HasSmallContrastGradientScaleBound alpha
      (smallContrastGradientConstant d * smallContrastDataSize d alpha u f) u := by
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha.1
  have hgradUnit : MemVectorL2 (smallContrastUnitBall d) u.grad :=
    u.grad_memVectorL2
  have hgradNorm :
      vectorNormalizedL2On (smallContrastUnitBall d) u.grad ≤
        smallContrastUnitBallVolumePrice d *
          vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad := by
    simpa only [smallContrastUnitBall, one_mul, mul_one, Real.one_rpow] using
      (vectorNormalizedL2On_euclideanBall_le_price_mul_rpow_mul_globalLp
        (d := d) (U := smallContrastUnitBall d) (0 : Vec d)
        (r := 1) (p := 2) (f := u.grad) (by norm_num) (by norm_num)
        Set.Subset.rfl (by
          change MemLp (fun x => HilbertVec.ofVec (u.grad x))
            (ENNReal.ofReal 2) (volume.restrict (smallContrastUnitBall d))
          simpa only [ENNReal.ofReal_ofNat] using
            (memHilbertVectorL2_hilbertifyVecField hgradUnit)))
  have hdyadic := dyadicGradientScaleBound_on_interiorBall
    (d := d) (0 : Vec d) (R := 1) (by norm_num) Set.Subset.rfl
      hd halpha0 halpha.2 hdelta0 hdelta
      (isOpen_euclideanBall 0 (1 : ℝ)) hEll ha hu hf
  have hread := gradientScaleBound_of_dyadic (d := d) (0 : Vec d)
    (R := 1) (alpha := alpha) (by norm_num) halpha.2 hgradUnit hdyadic
  intro r hr hr1
  have hbase := hread r hr hr1.le
  let H : ℝ := (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)
  let P : ℝ := smallContrastUnitBallVolumePrice d
  let G : ℝ := vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad
  let F : ℝ := vectorLpSizeOn (smallContrastUnitBall d)
    (schauderSourceExponent d alpha) f
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (by norm_num) (by norm_num) (by
        have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
        linarith)
  have hP : 0 ≤ P := smallContrastUnitBallVolumePrice_nonneg d
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hgapInv : 0 ≤ (1 - alpha)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr halpha.2.le)
  have hK :
      H * (vectorNormalizedL2On (smallContrastUnitBall d) u.grad +
          16 * (1 - alpha)⁻¹ * (H * P) * F) ≤
        16 * H ^ 2 * P * (G + (1 - alpha)⁻¹ * F) := by
    have hfirst : H * vectorNormalizedL2On (smallContrastUnitBall d) u.grad ≤
        H * P * G := by
      dsimp only [H, P, G]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hgradNorm (le_trans zero_le_one hH))
    have henlarge : H * P * G ≤ 16 * H ^ 2 * P * G := by
      have hHPG : 0 ≤ H * P * G :=
        mul_nonneg (mul_nonneg (le_trans zero_le_one hH) hP) hG
      have hHsq : H * P * G ≤ H ^ 2 * P * G := by
        have := mul_le_mul_of_nonneg_right hH hHPG
        nlinarith
      nlinarith [hHsq, mul_nonneg (mul_nonneg (sq_nonneg H) hP) hG]
    calc
      H * (vectorNormalizedL2On (smallContrastUnitBall d) u.grad +
          16 * (1 - alpha)⁻¹ * (H * P) * F)
          = H * vectorNormalizedL2On (smallContrastUnitBall d) u.grad +
              H * (16 * (1 - alpha)⁻¹ * (H * P) * F) := by ring
      _ ≤ H * P * G + H * (16 * (1 - alpha)⁻¹ * (H * P) * F) :=
        add_le_add hfirst le_rfl
      _ ≤ 16 * H ^ 2 * P * G +
          H * (16 * (1 - alpha)⁻¹ * (H * P) * F) :=
        add_le_add henlarge le_rfl
      _ = 16 * H ^ 2 * P * (G + (1 - alpha)⁻¹ * F) := by ring
  calc
    r ^ (1 - alpha) * vectorNormalizedL2On (smallContrastBall d r) u.grad ≤
        H * (vectorNormalizedL2On (smallContrastUnitBall d) u.grad +
          16 * (1 - alpha)⁻¹ * (H * P) * F) := by
      simpa only [smallContrastBall, smallContrastDyadicRadius_zero,
        Real.one_rpow, one_mul, H, P, F] using hbase
    _ ≤ 16 * H ^ 2 * P * (G + (1 - alpha)⁻¹ * F) := hK
    _ = smallContrastGradientConstant d * smallContrastDataSize d alpha u f := by
      dsimp only [smallContrastGradientConstant, smallContrastDataSize, H, P, G, F]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
