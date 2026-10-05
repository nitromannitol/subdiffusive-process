module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductUniformPrice

@[expose] public section

/-!
# Theta-perturbed ladder: linear two-scale comparison

This is the form consumed by the excess recurrence.  On the unit product-
error range, the normalized comparison error is a dimension-only constant
times the inner product error and the centered parent `L²` oscillation.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Dimension-only coefficient in the linear product comparison. -/
def productComparisonLinearConstant (d : ℕ) [NeZero d] (hd : 2 ≤ d) : ℝ :=
  (flatComparatorSharpSpectralConstant d).toReal *
    productFlatLinearConstant (productFlatComparatorConstant d hd) *
    productUniformWeightedConstant d / 9

theorem productComparisonLinearConstant_nonneg
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    0 ≤ productComparisonLinearConstant d hd := by
  unfold productComparisonLinearConstant
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg
        (productFlatLinearConstant_nonneg _))
      (by
        unfold productUniformWeightedConstant
        exact mul_nonneg
          (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
          (Real.sqrt_nonneg _)))
    (by norm_num)

/-- Linearized two-scale product comparison on the unit error range. -/
theorem exists_productTwoScaleFlatComparator_linear
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B)
    {b epsilon alpha Ebase c : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hb : 0 < b)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (m : ℤ)
    (hparentB : openCubeSet (originCube d (m + 2)) ⊆ B)
    (u : H1Function (openCubeSet (originCube d (m + 2))))
    (hu : IsWeaklyHarmonicOn
      (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x)
      (openCubeSet (originCube d (m + 2))) u)
    (hbaseParent : paperHomogenizationError
      (originCube d (m + 2)) (originCube d (m + 2)).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase)
    (hbaseInner : paperHomogenizationError
      (originCube d m) (originCube d m).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase)
    (hparentOne :
      (paperHomogenizationError
        (originCube d (m + 2)) (originCube d (m + 2)).scale
        ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta
          hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal ≤ 1) :
    let A := localizedThetaCoeffFamily M L omega hB theta htheta
      hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear
    let Einner := (paperHomogenizationError
      (originCube d m) (originCube d m).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2) A alpha).toReal
    let uInner := productConcentricInnerH1 d m u
    ∃ v : H1Function (openCubeSet (originCube d m)),
      Section6Schauder.IsUnitWeaklyHarmonicOn
        (openCubeSet (originCube d m)) v ∧
      Ch03.ABK26.HasH10Difference (originCube d m) uInner v ∧
      cubeLpNorm (originCube d m) 2
          (fun x ↦ uInner.toFun x - v.toFun x) ≤
        productComparisonLinearConstant d hd * Einner *
          normalizedL2On (openCubeSet (originCube d (m + 2)))
            (fun x ↦ u.toFun x - c) := by
  dsimp only
  let A := localizedThetaCoeffFamily M L omega hB theta htheta
    hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear
  let Eparent := (paperHomogenizationError
    (originCube d (m + 2)) (originCube d (m + 2)).scale
    ((3 / 16 : ℝ) / 6) .infinity (.finite 2) A alpha).toReal
  let Einner := (paperHomogenizationError
    (originCube d m) (originCube d m).scale
    ((3 / 16 : ℝ) / 6) .infinity (.finite 2) A alpha).toReal
  let uInner := productConcentricInnerH1 d m u
  let S := productComparisonWeightedPrice d alpha Eparent c m u
  let R := (flatComparatorLocalCoarseBound
    (productFlatComparatorConstant d hd) alpha
    productMiddleOrder productLowOrder productHighOrder
    Einner Einner S 0 (m - 1)).toReal
  obtain ⟨v, hv, huv, hraw⟩ := productTwoScaleFlatComparator
    d hd M L omega hB theta htheta hb hepsilon hepsilonHalf hnear halpha
      m hparentB u hu hbaseParent hbaseInner
  have hEparent0 : 0 ≤ Eparent := ENNReal.toReal_nonneg
  have hEinner0 : 0 ≤ Einner := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ S := by
    dsimp only [S, productComparisonWeightedPrice]
    exact mul_nonneg
      (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
      (Real.sqrt_nonneg _)
  have hS : S ≤ productUniformWeightedConstant d * Real.sqrt alpha *
      Real.rpow (3 : ℝ)
        (-(((originCube d (m + 2)).scale : ℤ) : ℝ)) *
      normalizedL2On (openCubeSet (originCube d (m + 2)))
        (fun x ↦ u.toFun x - c) := by
    exact productComparisonWeightedPrice_le_uniform halpha hEparent0
      (by simpa only [Eparent, A] using hparentOne)
  let T := productFlatLinearConstant (productFlatComparatorConstant d hd) *
    Real.sqrt alpha * Einner *
      (productUniformWeightedConstant d * Real.sqrt alpha *
        Real.rpow (3 : ℝ)
          (-(((originCube d (m + 2)).scale : ℤ) : ℝ)) *
        normalizedL2On (openCubeSet (originCube d (m + 2)))
          (fun x ↦ u.toFun x - c))
  have hR : R ≤ T := by
    have hlocal := productFlatLocalCoarseBound_toReal_le
      (productFlatComparatorConstant d hd) (m - 1) halpha hEinner0 hS0
    have hcoef : 0 ≤
        productFlatLinearConstant (productFlatComparatorConstant d hd) *
          Real.sqrt alpha * Einner := by
      exact mul_nonneg
        (mul_nonneg (productFlatLinearConstant_nonneg _) (Real.sqrt_nonneg _))
        hEinner0
    exact hlocal.trans (by
      dsimp only [T]
      exact mul_le_mul_of_nonneg_left hS hcoef)
  have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
  have hscale0 : 0 ≤ centeredCubeScale m := (centeredCubeScale_pos m).le
  have houter := productSpectralReadout_mono (d := d) halpha
    (mul_nonneg hscale0 hR0)
    (mul_le_mul_of_nonneg_left hR hscale0)
  have houter' :
      (flatComparatorSharpSpectralConstant d *
        ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ * R)).toReal ≤
      (flatComparatorSharpSpectralConstant d).toReal * alpha⁻¹ *
        (centeredCubeScale m * T) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using houter
  refine ⟨v, hv, huv, hraw.trans ?_⟩
  have hsqrt : Real.sqrt alpha * Real.sqrt alpha = alpha :=
    Real.mul_self_sqrt halpha.le
  have hscale := centeredCubeScale_mul_productParentInvScale (d := d) m
  calc
    (flatComparatorSharpSpectralConstant d *
        ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ * R)).toReal ≤
      (flatComparatorSharpSpectralConstant d).toReal * alpha⁻¹ *
        (centeredCubeScale m * T) := houter'
    _ = productComparisonLinearConstant d hd * Einner *
        normalizedL2On (openCubeSet (originCube d (m + 2)))
          (fun x ↦ u.toFun x - c) := by
      dsimp only [T, productComparisonLinearConstant]
      calc
        _ = (flatComparatorSharpSpectralConstant d).toReal *
            productFlatLinearConstant (productFlatComparatorConstant d hd) *
            productUniformWeightedConstant d * alpha⁻¹ *
            (Real.sqrt alpha * Real.sqrt alpha) *
            (centeredCubeScale m * Real.rpow (3 : ℝ)
              (-(((originCube d (m + 2)).scale : ℤ) : ℝ))) *
            Einner * normalizedL2On
              (openCubeSet (originCube d (m + 2)))
              (fun x ↦ u.toFun x - c) := by ring
        _ = _ := by
          rw [hsqrt, hscale]
          field_simp [halpha.ne']

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
