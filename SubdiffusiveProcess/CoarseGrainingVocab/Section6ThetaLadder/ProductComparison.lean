import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductEllipticityEnergy
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductEnergyReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.Restriction




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The fixed fractional orders used by the product comparison. -/
def productLowOrder : FractionalOrder :=
  ⟨(3 / 16 : ℝ) / 3, by norm_num, by norm_num⟩

def productMiddleOrder : FractionalOrder :=
  ⟨(3 / 16 : ℝ) / 2, by norm_num, by norm_num⟩

def productHighOrder : FractionalOrder := ⟨3 / 16, by norm_num, by norm_num⟩

/-- The root-energy price furnished by the parent two-scale Caccioppoli row. -/
def productComparisonRootPrice (d : ℕ) [NeZero d]
    (alpha E c : ℝ) (m : ℤ)
    (u : H1Function (openCubeSet (originCube d (m + 2)))) : ℝ :=
  productRootEnergyPrefactor d (productCaccioppoliConstant d) E *
    (productLocalEllipticityCap d E * alpha * Real.rpow (3 : ℝ)
      (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) *
      normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
        (fun x ↦ u.toFun x - c))

/-- The weighted-energy price inserted into the sharp comparator. -/
def productComparisonWeightedPrice (d : ℕ) [NeZero d]
    (alpha E c : ℝ) (m : ℤ)
    (u : H1Function (openCubeSet (originCube d (m + 2)))) : ℝ :=
  Section6Dirichlet.dirichletWeightedEnergyFactor
      productLowOrder.1 productMiddleOrder.1 *
    Real.sqrt (productComparisonRootPrice d alpha E c m u)

/-- The dimension-only sharp-comparator constant selected once for the theta
ladder. -/
noncomputable def productFlatComparatorConstant (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) : ℝ≥0∞ :=
  Classical.choose (exists_productFlatComparator_sharp d hd)

theorem productFlatComparatorConstant_lt_top (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) : productFlatComparatorConstant d hd < ∞ :=
  (Classical.choose_spec (exists_productFlatComparator_sharp d hd)).1

/-- A homogeneous product solution on the parent cube admits a unit-harmonic
comparison on the cube two scales below.  The only stochastic inputs are the
base-family paper-error caps on those two cubes; all product-coefficient
energy and ellipticity slots are discharged internally. -/
theorem productTwoScaleFlatComparator
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
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
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (openCubeSet (originCube d (m + 2))) u)
    (hbaseParent : paperHomogenizationError
      (originCube d (m + 2)) (originCube d (m + 2)).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase)
    (hbaseInner : paperHomogenizationError
      (originCube d m) (originCube d m).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase) :
      let A := localizedThetaCoeffFamily M L omega hB theta htheta
        hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear
      let Etheta := (paperHomogenizationError
        (originCube d (m + 2)) (originCube d (m + 2)).scale
        ((3 / 16 : ℝ) / 6) .infinity (.finite 2) A alpha).toReal
      let uInner := productConcentricInnerH1 d m u
      let S := productComparisonWeightedPrice d alpha Etheta c m u
      ∃ v : H1Function (openCubeSet (originCube d m)),
        Section6Schauder.IsUnitWeaklyHarmonicOn
          (openCubeSet (originCube d m)) v ∧
        Ch03.ABK26.HasH10Difference (originCube d m) uInner v ∧
        cubeLpNorm (originCube d m) 2
            (fun x ↦ uInner.toFun x - v.toFun x) ≤
          (flatComparatorSharpSpectralConstant d *
            ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ *
              (flatComparatorLocalCoarseBound (productFlatComparatorConstant d hd) alpha
                productMiddleOrder productLowOrder productHighOrder
                (paperHomogenizationError
                  (originCube d m) (originCube d m).scale
                  ((3 / 16 : ℝ) / 6) .infinity (.finite 2) A alpha).toReal
                (paperHomogenizationError
                  (originCube d m) (originCube d m).scale
                  ((3 / 16 : ℝ) / 6) .infinity (.finite 2) A alpha).toReal
                S 0 (m - 1)).toReal)).toReal := by
  have hflat :=
    (Classical.choose_spec (exists_productFlatComparator_sharp d hd)).2
  dsimp only
  let A := localizedThetaCoeffFamily M L omega hB theta htheta
    hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear
  let Qbig := originCube d (m + 2)
  let Q := originCube d m
  let uInner := productConcentricInnerH1 d m u
  let Etheta := (paperHomogenizationError Qbig Qbig.scale
    ((3 / 16 : ℝ) / 6) .infinity (.finite 2) A alpha).toReal
  let S := productComparisonWeightedPrice d alpha Etheta c m u
  have huBig : Ch03.ABK26.IsForcedEquation Qbig (A.coeffOn Qbig) u
      (fun _ ↦ 0) := by
    exact isForcedEquation_localizedThetaCoeffFamily_of_physical
      M L omega hB (b := b) (epsilon := epsilon) (hb := hb)
      theta htheta hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear
      Qbig hparentB u hu
  have hproductError : Ch02.HomogenizationErrorOnCube Qbig (1 / 32 : ℝ)
      .infinity (.finite 2) A (scalarMatrix (d := d) alpha) ≤ Etheta := by
    have hraw := homogenizationErrorOnCube_localizedTheta_le_paper_toReal
      M L omega hB (s := (1 / 32 : ℝ)) theta htheta
        hepsilon hepsilonHalf hnear halpha
        (by norm_num) Qbig (by
          simpa only [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num] using hbaseParent)
    simpa only [A, Etheta,
      show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num] using hraw
  have hroot := productConcentricRootEnergyBound d A m u alpha Etheta c
    halpha huBig hproductError
  have hweighted : weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
      (A.coeffOn Q) uInner productLowOrder productMiddleOrder
        FiniteLpExponent.two ≤ ENNReal.ofReal S := by
    apply weightedLocalSymmetricEnergyLp_localizedTheta_le_of_rootEnergy
      M L omega hB theta htheta hepsilon.le
        (hepsilonHalf.trans_lt (by norm_num)) hnear Q uInner
        productLowOrder productMiddleOrder (by
          norm_num [productLowOrder, productMiddleOrder])
    simpa only [Qbig, Q, A, uInner, Etheta, S,
      productComparisonWeightedPrice, productComparisonRootPrice] using hroot
  have hsub : openCubeSet Q ⊆ openCubeSet Qbig :=
    openCubeSet_originCube_subset_of_scale_le (by omega)
  have huInnerPhysical : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (openCubeSet Q) uInner := by
    exact Section6BoundaryL2.isWeaklyHarmonicOn_restrict
      (isOpen_openCubeSet Qbig) (isOpen_openCubeSet Q) hsub hu
  have huInner : Ch03.ABK26.IsForcedEquation Q (A.coeffOn Q) uInner
      (fun _ ↦ 0) := by
    exact isForcedEquation_localizedThetaCoeffFamily_of_physical
      M L omega hB (b := b) (epsilon := epsilon) (hb := hb)
      theta htheta hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear
      Q (hsub.trans hparentB) uInner huInnerPhysical
  have hout := hflat M L omega hB theta htheta hepsilon hepsilonHalf hnear
    halpha (by norm_num : (0 : ℝ) < 3 / 16)
    (by norm_num : (3 / 16 : ℝ) < 1) (by norm_num : (3 / 16 : ℝ) ≤ 1 / 4)
    m uInner huInner hbaseInner hweighted
  simpa only [A, Qbig, Q, uInner, Etheta, S, productLowOrder,
    productMiddleOrder, productHighOrder] using hout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
