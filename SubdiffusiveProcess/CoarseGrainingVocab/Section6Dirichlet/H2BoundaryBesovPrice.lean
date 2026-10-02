import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.H2BoundaryDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PositiveBesovFullDatum

/-!
# Full positive-Besov price for the physical `H²` boundary datum

The Chapter 3 energy consequence charges the full positive Besov norm of
the boundary gradient.  This file combines the top-scale `L²` dilation,
the arbitrary-scale exact fractional price, and the frozen `H2Datum.norm`
budget.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- Exact normalized Euclidean `L²` scaling of the physical vector datum. -/
theorem cubeEuclideanNormalizedLpENorm_centeredCubeScaledVectorDilation_eq
    {d : ℕ} (alpha : ℝ) (m : ℤ)
    (F : CubeVectorH1Function (originCube d 0)) :
    (cubeBoundedMeasurableDomain (originCube d m)).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) (centeredCubeScaledVectorDilation alpha m F).toField =
      ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
        (unitCenteredCubeDomain d).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) (unitEuclideanL2FieldOfCubeVectorH1 F) := by
  have hcube : Homogenization.Book.Ch02.dilateCube m (originCube d 0) =
      originCube d m := by
    simp [Homogenization.Book.Ch02.dilateCube, originCube]
  have hdilate := cubeEuclideanNormalizedLpENorm_dilate m (originCube d 0)
    FiniteLpExponent.two (centeredCubeScaledVectorDilation alpha m F).toField
  rw [hcube] at hdilate
  have hdilate' :
      (cubeBoundedMeasurableDomain (originCube d m)).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) (centeredCubeScaledVectorDilation alpha m F).toField =
        (cubeBoundedMeasurableDomain (originCube d 0)).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) (fun x ↦
            (centeredCubeScaledVectorDilation alpha m F).toField
              (Homogenization.Book.Ch02.dilateVec m x)) := by
    simpa only [FiniteLpExponent.two_exponent] using hdilate
  rw [hdilate']
  have hfield :
      (fun x ↦ (centeredCubeScaledVectorDilation alpha m F).toField
        (Homogenization.Book.Ch02.dilateVec m x)) =
        (fun x ↦ (alpha * (centeredCubeScale m)⁻¹) • F.toField x) := by
    funext x
    rw [centeredCubeScaledVectorDilation_toField]
    have hscale : Homogenization.Book.Ch02.triadicDilationFactor m =
        centeredCubeScale m := rfl
    rw [Homogenization.Book.Ch02.dilateVec, hscale, smul_smul,
      inv_mul_cancel₀ (centeredCubeScale_ne_zero m), one_smul]
  rw [hfield]
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpENorm
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  simp only [unitCenteredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    unitEuclideanL2FieldOfCubeVectorH1_apply, euclideanNorm_eq_norm_ofVec]
  rw [eLpNorm_norm, eLpNorm_norm]
  rw [show (fun x ↦ HilbertVec.ofVec
      ((alpha * (centeredCubeScale m)⁻¹) • F.toField x)) =
      (alpha * (centeredCubeScale m)⁻¹) •
        (fun x ↦ HilbertVec.ofVec (F.toField x)) by
      funext x
      simp only [Pi.smul_apply]
      ext i
      rfl]
  exact eLpNorm_const_smul _ _ _ _

/-- Extended-real top-scale `L²` price of the physical boundary gradient. -/
noncomputable def h2BoundaryGradientL2ENormBound
    {d : ℕ} (m : ℤ) (h : H2Datum (originCube d 0)) : ℝ≥0∞ :=
  ‖(centeredCubeScale m)⁻¹‖ₑ *
    (h2DatumGradientBudgetConstant d * h.norm)

/-- Extended-real exact fractional price of the physical boundary gradient. -/
noncomputable def h2BoundaryGradientWspENormBound
    {d : ℕ} (m : ℤ) (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) : ℝ≥0∞ :=
  (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
    ‖(centeredCubeScale m)⁻¹‖ₑ *
      (euclideanHsToContinuousKSeminormConstant s d *
        ((h2DatumGradientBudgetConstant d * h.norm) *
          max 1 (linearKSeminormConstant s)))

theorem h2BoundaryGradientL2ENormBound_lt_top
    {d : ℕ} (m : ℤ) (h : H2Datum (originCube d 0)) :
    h2BoundaryGradientL2ENormBound m h < ∞ := by
  unfold h2BoundaryGradientL2ENormBound
  exact ENNReal.mul_lt_top enorm_lt_top
    (ENNReal.mul_lt_top (h2DatumGradientBudgetConstant_lt_top d)
      (h2Datum_norm_lt_top h))

theorem h2BoundaryGradientWspENormBound_lt_top
    {d : ℕ} (m : ℤ) (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) :
    h2BoundaryGradientWspENormBound m s h < ∞ := by
  have hscale : (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) < ∞ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rcases ENNReal.rpow_eq_top_iff.mp htop with hzero | htop'
    · exact (ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos m)) hzero.1
    · exact ENNReal.ofReal_ne_top htop'.1
  unfold h2BoundaryGradientWspENormBound
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hscale enorm_lt_top)
    (ENNReal.mul_lt_top
      (euclideanHsToContinuousKSeminormConstant_lt_top s d)
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (h2DatumGradientBudgetConstant_lt_top d)
          (h2Datum_norm_lt_top h))
        (max_lt_iff.mpr ⟨ENNReal.one_lt_top,
          linearKSeminormConstant_lt_top s⟩)))

theorem normalizedEuclideanLpENorm_h2DatumGradientDilation_le
    {d : ℕ} (m : ℤ) (h : H2Datum (originCube d 0)) :
    (cubeBoundedMeasurableDomain (originCube d m)).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) (centeredCubeScaledVectorDilation 1 m
          (h2DatumGradientH1 h)).toField ≤
      h2BoundaryGradientL2ENormBound m h := by
  rw [cubeEuclideanNormalizedLpENorm_centeredCubeScaledVectorDilation_eq]
  have hunit :
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
          (unitEuclideanL2FieldOfCubeVectorH1 (h2DatumGradientH1 h)) ≤
        h2DatumGradientBudgetConstant d * h.norm := by
    exact (le_add_right le_rfl).trans
      (unitCubeVectorH1ENormBudget_h2DatumGradient_le h)
  unfold h2BoundaryGradientL2ENormBound
  simpa only [one_mul] using mul_le_mul_right hunit
    ‖(centeredCubeScale m)⁻¹‖ₑ

theorem cubeEuclideanWspESeminorm_h2DatumGradientDilation_le
    {d : ℕ} (m : ℤ) (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) :
    cubeEuclideanWspESeminorm (originCube d m) s FiniteLpExponent.two
        (centeredCubeScaledVectorDilation 1 m
          (h2DatumGradientH1 h)).toField ≤
      h2BoundaryGradientWspENormBound m s h := by
  let U : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      (unitEuclideanL2FieldOfCubeVectorH1 (h2DatumGradientH1 h))
  let H : ℝ≥0∞ := ENNReal.ofReal (h2DatumGradientH1 h).gradientCoordL2NormSum
  let K : ℝ≥0∞ := max 1 (linearKSeminormConstant s)
  let B : ℝ≥0∞ := h2DatumGradientBudgetConstant d * h.norm
  have hUK : U + H * linearKSeminormConstant s ≤ (U + H) * K := by
    calc
      U + H * linearKSeminormConstant s ≤ U * K + H * K := by
        exact add_le_add
          (by simpa only [K, one_mul, mul_comm] using
            mul_le_mul_left (le_max_left 1 (linearKSeminormConstant s)) U)
          (by simpa only [K, mul_comm] using
            mul_le_mul_left (le_max_right 1 (linearKSeminormConstant s)) H)
      _ = (U + H) * K := by ring
  have hbudget : U + H ≤ B := by
    simpa only [U, H, B, unitCubeVectorH1ENormBudget] using
      unitCubeVectorH1ENormBudget_h2DatumGradient_le h
  have hinner : U + H * linearKSeminormConstant s ≤ B * K :=
    hUK.trans (by simpa only [mul_comm] using mul_le_mul_right hbudget K)
  have hraw := cubeEuclideanWspESeminorm_centeredCubeScaledVectorDilation_le
    1 m s (h2DatumGradientH1 h)
  calc
    _ ≤ (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        ‖1 * (centeredCubeScale m)⁻¹‖ₑ *
          (euclideanHsToContinuousKSeminormConstant s d *
            (U + H * linearKSeminormConstant s)) := by
      simpa only [U, H] using hraw
    _ ≤ (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        ‖1 * (centeredCubeScale m)⁻¹‖ₑ *
          (euclideanHsToContinuousKSeminormConstant s d * (B * K)) := by
      gcongr
    _ = h2BoundaryGradientWspENormBound m s h := by
      simp only [one_mul]
      rfl

/-- Real right-hand side obtained by combining the top-scale and exact
fractional prices. -/
noncomputable def h2BoundaryPositiveBesovBound
    {d : ℕ} (m : ℤ) (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) : ℝ :=
  (d : ℝ) * (h2BoundaryGradientL2ENormBound m h).toReal +
    caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1)
        (originCube d m) *
      (h2BoundaryGradientWspENormBound m s h).toReal

/-- The literal full boundary-gradient norm on the physical cube is bounded
by a finite expression depending only on the frozen `H²` norm and fixed
dimension/order constants. -/
theorem scaleNormalizedPositiveBesovVectorNormTwo_h2DatumGradientDilation_le
    {d : ℕ} [NeZero d] (m : ℤ) (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) :
    scaleNormalizedPositiveBesovVectorNormTwo (originCube d m) s.1
        (centeredCubeScaledVectorDilation 1 m
          (h2DatumGradientH1 h)).toField ≤
      h2BoundaryPositiveBesovBound m s h := by
  let F : CubeEuclideanWspField (originCube d m) s FiniteLpExponent.two :=
    centeredCubeScaledVectorDilationWspField 1 m s (h2DatumGradientH1 h)
  have hbase := scaleNormalizedPositiveBesovVectorNormTwo_le_exactDatum_general
    (originCube d m) s F
  have hL := normalizedEuclideanLpENorm_h2DatumGradientDilation_le m h
  have hW := cubeEuclideanWspESeminorm_h2DatumGradientDilation_le m s h
  have hLreal :
      ((cubeBoundedMeasurableDomain (originCube d m)).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) F.toField).toReal ≤
        (h2BoundaryGradientL2ENormBound m h).toReal := by
    apply ENNReal.toReal_mono
      (h2BoundaryGradientL2ENormBound_lt_top m h).ne
    simpa only [F, centeredCubeScaledVectorDilationWspField_toField] using hL
  have hWreal :
      (cubeEuclideanWspESeminorm (originCube d m) s FiniteLpExponent.two
          F.toField).toReal ≤
        (h2BoundaryGradientWspENormBound m s h).toReal := by
    apply ENNReal.toReal_mono
      (h2BoundaryGradientWspENormBound_lt_top m s h).ne
    simpa only [F, centeredCubeScaledVectorDilationWspField_toField] using hW
  apply hbase.trans
  unfold h2BoundaryPositiveBesovBound
  exact add_le_add
    (mul_le_mul_of_nonneg_left hLreal (Nat.cast_nonneg _))
    (mul_le_mul_of_nonneg_left hWreal
      (mul_nonneg (caccioppoliExactDatumConstant_pos d).le
        (cubeBesovScaleWeight_nonneg _ _)))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
