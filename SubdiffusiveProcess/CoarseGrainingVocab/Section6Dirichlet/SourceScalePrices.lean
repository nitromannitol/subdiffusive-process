module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalPrebalance

@[expose] public section

/-!
# Source-scale normalization of the Dirichlet datum prices

The physical coarse-graining call is made on `□_N`, while both source data
live on `□_0`.  This file cancels the positive Besov scale weight against the
exact fractional dilation and exposes the remaining `3^{-N}` amplitude.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

theorem cubeBesovScaleWeight_neg_originCube_eq_centeredCubeScale_rpow
    {d : ℕ} (m : ℤ) (s : ℝ) :
    cubeBesovScaleWeight (-s) (originCube d m) =
      (centeredCubeScale m) ^ s := by
  simp only [cubeBesovScaleWeight, cubeScaleFactor_originCube, neg_neg]
  rfl

theorem centeredCubeScale_rpow_mul_ofReal_rpow_neg_toReal
    (m : ℤ) (s : ℝ) :
    (centeredCubeScale m) ^ s *
        ((ENNReal.ofReal (centeredCubeScale m)) ^ (-s)).toReal = 1 := by
  rw [← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (centeredCubeScale_pos m).le]
  rw [← Real.rpow_add (centeredCubeScale_pos m), add_neg_cancel,
    Real.rpow_zero]

theorem centeredCubeScale_mul_inv_eq_one (m : ℤ) :
    centeredCubeScale m * (centeredCubeScale m)⁻¹ = 1 :=
  mul_inv_cancel₀ (centeredCubeScale_ne_zero m)

/-- Exact amplitude/scale factorization of the forcing positive-Besov price. -/
theorem scaledVectorDatumPositiveBesovSeminormBound_eq_sourceScale
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    scaledVectorDatumPositiveBesovSeminormBound alpha m s F =
      |alpha| * (centeredCubeScale m)⁻¹ *
        scaledVectorDatumPositiveBesovSeminormBound 1 0 s F := by
  unfold scaledVectorDatumPositiveBesovSeminormBound
  unfold scaledVectorDatumWspENormBound
  rw [cubeBesovScaleWeight_neg_originCube_eq_centeredCubeScale_rpow,
    cubeBesovScaleWeight_neg_originCube_eq_centeredCubeScale_rpow]
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm,
    ENNReal.toReal_ofReal (centeredCubeScale_pos m).le,
    centeredCubeScale_zero, ENNReal.ofReal_one, ENNReal.toReal_one,
    one_mul, inv_one]
  have hcancel : (centeredCubeScale m) ^ s.1 *
      (centeredCubeScale m) ^ (-s.1) = 1 := by
    rw [← Real.rpow_add (centeredCubeScale_pos m), add_neg_cancel,
      Real.rpow_zero]
  have hnorm : ‖alpha * (centeredCubeScale m)⁻¹‖ =
      |alpha| * (centeredCubeScale m)⁻¹ := by
    rw [Real.norm_eq_abs, abs_mul, abs_inv,
      abs_of_pos (centeredCubeScale_pos m)]
  rw [hnorm, Real.one_rpow, norm_one]
  calc
    _ = ((centeredCubeScale m) ^ s.1 *
          (centeredCubeScale m) ^ (-s.1)) *
        (caccioppoliExactDatumConstant d *
          (|alpha| * (centeredCubeScale m)⁻¹) *
          (euclideanHsToContinuousKSeminormConstant s d).toReal *
          (max 1 (linearKSeminormConstant s)).toReal *
          (unitCubeVectorH1ENormBudget F).toReal) := by ring
    _ = _ := by rw [hcancel, one_mul]; simp only [Real.one_rpow]; ring

/-- Exact source-scale factorization of the full `H²` boundary-gradient
positive-Besov price. -/
theorem h2BoundaryPositiveBesovBound_eq_sourceScale
    {d : ℕ} (m : ℤ) (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) :
    h2BoundaryPositiveBesovBound m s h =
      (centeredCubeScale m)⁻¹ * h2BoundaryPositiveBesovBound 0 s h := by
  unfold h2BoundaryPositiveBesovBound
  unfold h2BoundaryGradientL2ENormBound h2BoundaryGradientWspENormBound
  rw [cubeBesovScaleWeight_neg_originCube_eq_centeredCubeScale_rpow,
    cubeBesovScaleWeight_neg_originCube_eq_centeredCubeScale_rpow]
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm,
    ENNReal.toReal_ofReal (centeredCubeScale_pos m).le,
    centeredCubeScale_zero, ENNReal.ofReal_one, ENNReal.toReal_one,
    one_mul, inv_one, norm_one]
  have hcancel : (centeredCubeScale m) ^ s.1 *
      (centeredCubeScale m) ^ (-s.1) = 1 := by
    rw [← Real.rpow_add (centeredCubeScale_pos m), add_neg_cancel,
      Real.rpow_zero]
  have hinvNorm : ‖(centeredCubeScale m)⁻¹‖ =
      (centeredCubeScale m)⁻¹ := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (centeredCubeScale_pos m)]
  rw [hinvNorm]
  calc
    _ = (centeredCubeScale m)⁻¹ *
        ((d : ℝ) * (h2DatumGradientBudgetConstant d).toReal * h.norm.toReal +
          caccioppoliExactDatumConstant d *
            ((centeredCubeScale m) ^ s.1 *
              (centeredCubeScale m) ^ (-s.1)) *
            (euclideanHsToContinuousKSeminormConstant s d).toReal *
            (h2DatumGradientBudgetConstant d).toReal * h.norm.toReal *
            (max 1 (linearKSeminormConstant s)).toReal) := by ring
    _ = _ := by
      rw [hcancel, mul_one]
      simp only [Real.one_rpow]
      ring

/-- Exact source-scale factorization of the positive fractional forcing
quantity supplied to the coarse-graining RHS. -/
theorem scaledVectorDatumFractionalBound_eq_sourceScale
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    scaledVectorDatumFractionalBound alpha m s F =
      (centeredCubeScale m) ^ (-s.1) *
        (|alpha| * (centeredCubeScale m)⁻¹) *
          scaledVectorDatumFractionalBound 1 0 s F := by
  unfold scaledVectorDatumFractionalBound
  unfold scaledVectorDatumFractionalENormBound
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm,
    ENNReal.toReal_ofReal (centeredCubeScale_pos m).le,
    centeredCubeScale_zero, ENNReal.ofReal_one, ENNReal.toReal_one,
    one_mul, inv_one]
  have hnorm : ‖alpha * (centeredCubeScale m)⁻¹‖ =
      |alpha| * (centeredCubeScale m)⁻¹ := by
    rw [Real.norm_eq_abs, abs_mul, abs_inv,
      abs_of_pos (centeredCubeScale_pos m)]
  rw [hnorm, norm_one]
  simp only [Real.one_rpow]
  ring

/-- Unit-scale coefficient of the forcing positive-Besov seminorm. -/
noncomputable def sourceForcingPositiveBesovConstant
    (d : ℕ) (s : FractionalOrder) : ℝ :=
  caccioppoliExactDatumConstant d *
    (euclideanHsToContinuousKSeminormConstant s d).toReal *
      (max 1 (linearKSeminormConstant s)).toReal

theorem sourceForcingPositiveBesovConstant_nonneg
    (d : ℕ) [NeZero d] (s : FractionalOrder) :
    0 ≤ sourceForcingPositiveBesovConstant d s := by
  unfold sourceForcingPositiveBesovConstant
  exact mul_nonneg
    (mul_nonneg (caccioppoliExactDatumConstant_pos d).le ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg

theorem scaledVectorDatumPositiveBesovSeminormBound_unit_eq
    {d : ℕ} (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    scaledVectorDatumPositiveBesovSeminormBound 1 0 s F =
      sourceForcingPositiveBesovConstant d s *
        (unitCubeVectorH1ENormBudget F).toReal := by
  unfold scaledVectorDatumPositiveBesovSeminormBound
    scaledVectorDatumWspENormBound sourceForcingPositiveBesovConstant
  rw [centeredCubeScale_zero]
  simp only [cubeBesovScaleWeight, cubeScaleFactor_originCube,
    zpow_zero, Real.one_rpow, ENNReal.ofReal_one, ENNReal.one_rpow,
    inv_one, one_mul, ENNReal.toReal_mul, toReal_enorm, norm_one]
  ring

/-- Unit-scale coefficient of the forcing fractional datum. -/
noncomputable def sourceForcingFractionalConstant
    (d : ℕ) (s : FractionalOrder) : ℝ :=
  (scaledVectorDatumFractionalConstant s d).toReal

theorem sourceForcingFractionalConstant_nonneg
    (d : ℕ) (s : FractionalOrder) :
    0 ≤ sourceForcingFractionalConstant d s := ENNReal.toReal_nonneg

theorem scaledVectorDatumFractionalBound_unit_eq
    {d : ℕ} (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    scaledVectorDatumFractionalBound 1 0 s F =
      sourceForcingFractionalConstant d s *
        (unitCubeVectorH1ENormBudget F).toReal := by
  unfold scaledVectorDatumFractionalBound scaledVectorDatumFractionalENormBound
    sourceForcingFractionalConstant
  rw [centeredCubeScale_zero]
  simp only [ENNReal.ofReal_one, ENNReal.one_rpow,
    inv_one, one_mul, ENNReal.toReal_mul, ENNReal.toReal_one,
    toReal_enorm, norm_one]
  ring

/-- Unit-scale coefficient of the full `H²` boundary-gradient Besov norm. -/
noncomputable def sourceBoundaryPositiveBesovConstant
    (d : ℕ) (s : FractionalOrder) : ℝ :=
  (d : ℝ) * (h2DatumGradientBudgetConstant d).toReal +
    caccioppoliExactDatumConstant d *
      (euclideanHsToContinuousKSeminormConstant s d).toReal *
      (h2DatumGradientBudgetConstant d).toReal *
      (max 1 (linearKSeminormConstant s)).toReal

theorem sourceBoundaryPositiveBesovConstant_nonneg
    (d : ℕ) [NeZero d] (s : FractionalOrder) :
    0 ≤ sourceBoundaryPositiveBesovConstant d s := by
  unfold sourceBoundaryPositiveBesovConstant
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (caccioppoliExactDatumConstant_pos d).le ENNReal.toReal_nonneg)
        ENNReal.toReal_nonneg)
      ENNReal.toReal_nonneg)

theorem h2BoundaryPositiveBesovBound_unit_eq
    {d : ℕ} (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) :
    h2BoundaryPositiveBesovBound 0 s h =
      sourceBoundaryPositiveBesovConstant d s * h.norm.toReal := by
  unfold h2BoundaryPositiveBesovBound h2BoundaryGradientL2ENormBound
    h2BoundaryGradientWspENormBound sourceBoundaryPositiveBesovConstant
  rw [centeredCubeScale_zero]
  simp only [inv_one, one_mul,
    cubeBesovScaleWeight, cubeScaleFactor_originCube, zpow_zero,
    Real.one_rpow, ENNReal.ofReal_one, ENNReal.one_rpow, ENNReal.toReal_mul,
    toReal_enorm, norm_one]
  ring

/-- Fully source-facing form of the positive-Besov forcing price. -/
theorem scaledVectorDatumPositiveBesovSeminormBound_eq_sourceDatum
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    scaledVectorDatumPositiveBesovSeminormBound alpha m s F =
      |alpha| * (centeredCubeScale m)⁻¹ *
        sourceForcingPositiveBesovConstant d s *
          (unitCubeVectorH1ENormBudget F).toReal := by
  rw [scaledVectorDatumPositiveBesovSeminormBound_eq_sourceScale,
    scaledVectorDatumPositiveBesovSeminormBound_unit_eq]
  ring

/-- Fully source-facing form of the fractional forcing price. -/
theorem scaledVectorDatumFractionalBound_eq_sourceDatum
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    scaledVectorDatumFractionalBound alpha m s F =
      (centeredCubeScale m) ^ (-s.1) *
        (|alpha| * (centeredCubeScale m)⁻¹) *
          sourceForcingFractionalConstant d s *
            (unitCubeVectorH1ENormBudget F).toReal := by
  rw [scaledVectorDatumFractionalBound_eq_sourceScale,
    scaledVectorDatumFractionalBound_unit_eq]
  ring

/-- Fully source-facing form of the positive-Besov boundary price. -/
theorem h2BoundaryPositiveBesovBound_eq_sourceDatum
    {d : ℕ} (m : ℤ) (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) :
    h2BoundaryPositiveBesovBound m s h =
      (centeredCubeScale m)⁻¹ * sourceBoundaryPositiveBesovConstant d s *
        h.norm.toReal := by
  rw [h2BoundaryPositiveBesovBound_eq_sourceScale,
    h2BoundaryPositiveBesovBound_unit_eq]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
