import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductEquation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductErrorBridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorSharpReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ForcedReplacement

/-!
# Theta-perturbed ladder: coefficient-generic flat comparison

This is the first analytic half of the raw product-coefficient recurrence.
It invokes the landed sharp comparator directly on
`localizedThetaCoeffFamily`, with zero force.  The only remaining analytic
input is the local weighted-energy row; no base-cutoff solution binder or
draft excess statement occurs here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem memCubeEuclideanFullWsp_zero
    (Q : TriadicCube d) (s : FractionalOrder) :
    MemCubeEuclideanFullWsp Q s FiniteLpExponent.two
      (fun _ ↦ (0 : Vec d)) := by
  constructor
  · exact MeasureTheory.memLp_const (μ := normalizedCubeMeasure Q)
      (p := (2 : ENNReal)) (0 : HilbertVec d)
  · have hkernel : cubeEuclideanWspKernel s FiniteLpExponent.two
        (fun _ ↦ (0 : Vec d)) = fun _ ↦ (0 : HilbertVec d) := by
      funext z
      rw [cubeEuclideanWspKernel_apply, sub_self]
      change _ • (HilbertVec.ofVecL d) 0 = 0
      rw [map_zero, smul_zero]
    rw [MemCubeEuclideanWsp, hkernel]
    exact MeasureTheory.memLp_const (μ := Gagliardo.gagliardoCubeMeasure Q)
      (p := FiniteLpExponent.two.exponent) (0 : HilbertVec d)

private theorem positiveBesovOverlap_zero
    (Q : TriadicCube d) (s : FractionalOrder) :
    Homogenization.cubeEuclideanPositiveBesovOverlapESeminorm
      Q s FiniteLpExponent.two
      (fun _ ↦ (0 : Vec d)) = 0 := by
  simp [Homogenization.cubeEuclideanPositiveBesovOverlapESeminorm]

private theorem isUnitWeaklyHarmonicOn_of_isScalarForcedEquation_zero
    {Q : TriadicCube d} {sigma : ℝ} (hsigma : 0 < sigma)
    (v : H1Function (openCubeSet Q))
    (hv : IsScalarForcedEquation Q sigma v (fun _ ↦ 0)) :
    IsUnitWeaklyHarmonicOn (openCubeSet Q) v := by
  intro phi
  have hphi := hv phi
  have hzero : -(∫ x in openCubeSet Q,
      vecDot (0 : Vec d) (phi.toH1Function.grad x) ∂volume) = 0 := by
    simp only [vecDot_zero_left, integral_zero, neg_zero]
  rw [hzero] at hphi
  simp only [matVecMul_scalarMatrix, vecDot_smul_left,
    MeasureTheory.integral_const_mul] at hphi
  exact (mul_eq_zero.mp hphi).resolve_left hsigma.ne'

variable [NeZero d]

/-- The sharp flat comparator specialized to the localized product family.
The replacement is genuinely unit harmonic because the scalar comparison
coefficient is a positive constant and the force vanishes. -/
theorem exists_productFlatComparator_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {B : Set (Vec d)} (hB : MeasurableSet B)
        {b epsilon alpha t Ebase S : ℝ}
        (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
        (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
        (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
        (halpha : 0 < alpha) (ht : 0 < t) (ht1 : t < 1)
        (htQuarter : t ≤ 1 / 4) (m : ℤ),
      let Q := originCube d m
      let A := localizedThetaCoeffFamily M L omega hB theta htheta
        hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear
      let s1 : FractionalOrder := ⟨t / 3, by positivity, by linarith⟩
      let smid : FractionalOrder := ⟨t / 2, by positivity, by linarith⟩
      let s2 : FractionalOrder := ⟨t, ht, ht1⟩
      ∀ u : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u (fun _ ↦ 0) →
        paperHomogenizationError Q Q.scale (t / 6) .infinity (.finite 2)
          (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase →
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ∃ v : H1Function (openCubeSet Q),
          IsUnitWeaklyHarmonicOn (openCubeSet Q) v ∧
          HasH10Difference Q u v ∧
          cubeLpNorm Q 2 (fun x ↦ u.toFun x - v.toFun x) ≤
            (flatComparatorSharpSpectralConstant d *
              ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ *
                (flatComparatorLocalCoarseBound C alpha smid s1 s2
                  (paperHomogenizationError Q Q.scale (t / 6)
                    .infinity (.finite 2) A alpha).toReal
                  (paperHomogenizationError Q Q.scale (t / 6)
                    .infinity (.finite 2) A alpha).toReal
                  S 0 (m - 1)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorManuscriptBound_sharp d hd
  refine ⟨C, hCtop, ?_⟩
  intro M L omega B hB b epsilon alpha t Ebase S theta htheta hepsilon
    hepsilonHalf hnear halpha ht ht1 htQuarter m
  dsimp only
  intro u hu hbase henergy
  let Q := originCube d m
  let g : Vec d → Vec d := fun _ ↦ 0
  have hg : MemCubeEuclideanFullWsp Q ⟨t, ht, ht1⟩
      FiniteLpExponent.two g := memCubeEuclideanFullWsp_zero Q ⟨t, ht, ht1⟩
  have hgL2 : MemVectorL2 (openCubeSet Q) g := by
    exact MeasureTheory.memLp_const (μ := volumeMeasureOn (openCubeSet Q))
      (p := (2 : ENNReal)) (0 : Vec d)
  let v := sourceForcedReplacement
    (scalarConstantCoeffMatrix (d := d) halpha) u hgL2
  have hv : IsScalarForcedEquation Q alpha v g :=
    isScalarForcedEquation_sourceForcedReplacement halpha u hgL2
  have huv : HasH10Difference Q u v :=
    hasH10Difference_sourceForcedReplacement
      (scalarConstantCoeffMatrix (d := d) halpha) u hgL2
  have hE := homogenizationErrorOnCube_localizedTheta_le_paper_toReal
    M L omega hB theta htheta hepsilon hepsilonHalf hnear halpha
      (by positivity : 0 < t / 6) Q hbase
  have hD : ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q
      ⟨t, ht, ht1⟩ FiniteLpExponent.two g ≤ ENNReal.ofReal 0 := by
    simpa [ABK26.cubeEuclideanPositiveBesovOverlapESeminorm, g] using
      le_of_eq (positiveBesovOverlap_zero Q ⟨t, ht, ht1⟩)
  have hout := hmain m t ht ht1 htQuarter
    (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
      (hepsilonHalf.trans_lt (by norm_num)) hnear)
    alpha halpha g hg u v hu hv huv
    (paperHomogenizationError Q Q.scale (t / 6) .infinity (.finite 2)
      (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
        (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal
    S 0 hE (by simpa [Q] using henergy) hD
  refine ⟨v, isUnitWeaklyHarmonicOn_of_isScalarForcedEquation_zero
    halpha v hv, huv, ?_⟩
  simpa only [Q, g, v] using hout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
