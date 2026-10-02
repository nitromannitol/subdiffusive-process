import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductCaccioppoli
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorPrefactorPrice

/-!
# Theta-perturbed ladder: product ellipticity and energy

The local product-family homogenization error controls the ellipticity slots
that occur in the coefficient-generic Caccioppoli estimate.  This file
performs that deterministic composition at flat order `s = 3/16`, whose
error slot `s/6 = 1/32` is exactly the fixed Holder-ladder good-event slot.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ}

/-- The inner two-scale restriction used by the product Caccioppoli row. -/
noncomputable def productConcentricInnerH1 (d : ℕ) (m : ℤ)
    (u : H1Function (openCubeSet (originCube d (m + 2)))) :
    H1Function (openCubeSet (originCube d m)) :=
  u.restrict (isOpen_openCubeSet (originCube d m))
    (openCubeSet_originCube_subset_of_scale_le (by omega))

/-- Ellipticity cap produced by a local product-error bound. -/
def productLocalEllipticityCap (d : ℕ) (E : ℝ) : ℝ :=
  2 * (d : ℝ) * (E ^ 2 + 1)

/-- Dimension/error prefactor in the product root-energy bound. -/
def productRootEnergyPrefactor (d : ℕ) (C E : ℝ) : ℝ :=
  (4 * max 1 C) ^ (8 : ℕ) * 8 *
    ((productLocalEllipticityCap d E) ^ 2) ^ (3 : ℕ)

/-- The coefficient-generic product root-energy interface at a fixed
Caccioppoli constant. -/
def ProductConcentricRootEnergyBound (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  ∀ (A : Ch02.TriadicCoeffFamily d) (m : ℤ)
        (u : H1Function (openCubeSet (originCube d (m + 2))))
        (alpha E c : ℝ),
      0 < alpha →
      Ch03.ABK26.IsForcedEquation (originCube d (m + 2))
          (A.coeffOn (originCube d (m + 2))) u (fun _ ↦ 0) →
      Ch02.HomogenizationErrorOnCube (originCube d (m + 2))
          (1 / 32 : ℝ) .infinity (.finite 2) A
          (scalarMatrix (d := d) alpha) ≤ E →
      cubeAverage (originCube d m)
          (coefficientEnergyDensity
            (A.coeffOn (originCube d m)).toCoeffField
            (productConcentricInnerH1 d m u).grad) ≤
        productRootEnergyPrefactor d C E *
          (productLocalEllipticityCap d E * alpha * Real.rpow (3 : ℝ)
            (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
              (fun x ↦ u.toFun x - c))

/-- The dimension-only Caccioppoli constant used by the product ladder. -/
noncomputable def productCaccioppoliConstant (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose (exists_concentricRootEnergy_le_caccioppoli d)

theorem productCaccioppoliConstant_pos (d : ℕ) [NeZero d] :
    0 < productCaccioppoliConstant d :=
  (Classical.choose_spec (exists_concentricRootEnergy_le_caccioppoli d)).1

/-- The two fixed-order ellipticity entries read directly from the local
product homogenization error. -/
theorem productFixedEllipticityCaps
    [NeZero d] (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    {alpha E : ℝ} (halpha : 0 < alpha)
    (herror : Ch02.HomogenizationErrorOnCube Q (1 / 32 : ℝ)
      .infinity (.finite 2) A (scalarMatrix (d := d) alpha) ≤ E) :
    Ch02.LambdaS Q (1 / 2) A ≤ productLocalEllipticityCap d E * alpha ∧
      alpha * (Ch02.lambdaSq Q (1 / 32) (.finite 2) A)⁻¹ ≤
        productLocalEllipticityCap d E := by
  have hlocal := localBoundaryEllipticityCaps_of_errorCap
    Q A (s := (3 / 16 : ℝ)) (sigma := alpha) (E₀ := E)
      (by norm_num) (by norm_num) halpha (by
        simpa only [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num] using herror)
  exact ⟨hlocal.2.2.1, by
    simpa only [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num] using hlocal.2.1⟩

/-- Fixed `(1/2,3/32)` Caccioppoli caps furnished by a local product error. -/
theorem productInteriorHalfEllipticityCaps
    [NeZero d] (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    {alpha E : ℝ} (halpha : 0 < alpha)
    (herror : Ch02.HomogenizationErrorOnCube Q (1 / 32 : ℝ)
      .infinity (.finite 2) A (scalarMatrix (d := d) alpha) ≤ E) :
    Ch02.lambdaS Q (3 / 32) A ≤ productLocalEllipticityCap d E * alpha ∧
      Ch02.ThetaRatio Q (1 / 2) (3 / 32) A ≤
        productLocalEllipticityCap d E ^ (2 : ℕ) := by
  obtain ⟨hupper, hlower⟩ := productFixedEllipticityCaps Q A halpha herror
  have hlower' : alpha *
      (Ch02.lambdaSq Q ((3 / 16 : ℝ) / 6) (.finite 2) A)⁻¹ ≤
        productLocalEllipticityCap d E := by
    simpa only [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num] using hlower
  have hhalf := interiorHalfEllipticityCaps_of_sixth Q A
    (s := (3 / 16 : ℝ)) (sigma := alpha)
    (B := productLocalEllipticityCap d E)
      (by norm_num) halpha hupper hlower'
  exact ⟨by
    simpa only [show (3 / 16 : ℝ) / 2 = 3 / 32 by norm_num] using hhalf.2.1,
    by simpa only [show (3 / 16 : ℝ) / 2 = 3 / 32 by norm_num] using hhalf.2.2⟩

/-- The local product-error cap closes the product root-energy interface for
the selected dimension-only Caccioppoli constant. -/
theorem productConcentricRootEnergyBound
    (d : ℕ) [NeZero d] :
    ProductConcentricRootEnergyBound d (productCaccioppoliConstant d) := by
  unfold ProductConcentricRootEnergyBound
  intro A m u alpha E c halpha hu herror
  let C := productCaccioppoliConstant d
  have hC : 0 < C := productCaccioppoliConstant_pos d
  let Qbig := originCube d (m + 2)
  let Q := originCube d m
  let B : ℝ := productLocalEllipticityCap d E
  have hhalf := productInteriorHalfEllipticityCaps Qbig A halpha herror
  have htheta : Ch02.ThetaRatio Qbig (1 / 2) ((3 / 16 : ℝ) / 2) A ≤
      B ^ (2 : ℕ) := by
    simpa only [show (3 / 16 : ℝ) / 2 = 3 / 32 by norm_num, B] using hhalf.2
  have hpref := caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Qbig) (A := A) hC (by norm_num : (0 : ℝ) < 3 / 16)
      (by norm_num : (3 / 16 : ℝ) ≤ 1 / 4) htheta
  have hpref' : caccioppoliWithRHSPrefactor
      (productCaccioppoliConstant d) (originCube d (m + 2)) A
        (1 / 2) (3 / 32) ≤
      productRootEnergyPrefactor d (productCaccioppoliConstant d) E := by
    simpa only [C, Qbig, B, productRootEnergyPrefactor,
      show (3 / 16 : ℝ) / 2 = 3 / 32 by norm_num] using hpref
  have hlam : Ch02.lambdaS Qbig (3 / 32 : ℝ) A ≤ B * alpha := by
    simpa only [B] using hhalf.1
  have hscale : 0 ≤ Real.rpow (3 : ℝ)
      (-2 * (((Qbig.scale : ℤ) : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hnorm : 0 ≤ normalizedL2SqOnSet (openCubeSet Qbig)
      (fun x ↦ u.toFun x - c) :=
    normalizedL2SqOnSet_nonneg (openCubeSet Qbig) _
      (measurableSet_openCubeSet Qbig)
  have hinner :
      Ch02.lambdaS Qbig (3 / 32 : ℝ) A *
          Real.rpow (3 : ℝ) (-2 * (((Qbig.scale : ℤ) : ℝ))) *
          normalizedL2SqOnSet (openCubeSet Qbig) (fun x ↦ u.toFun x - c) ≤
        B * alpha *
          Real.rpow (3 : ℝ) (-2 * (((Qbig.scale : ℤ) : ℝ))) *
          normalizedL2SqOnSet (openCubeSet Qbig) (fun x ↦ u.toFun x - c) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlam hscale) hnorm
  have hlam0 : 0 ≤ Ch02.lambdaS Qbig (3 / 32 : ℝ) A := by
    rw [Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_nonneg Qbig A (by norm_num) (by norm_num)
  have hinner0 : 0 ≤
      Ch02.lambdaS Qbig (3 / 32 : ℝ) A *
        Real.rpow (3 : ℝ) (-2 * (((Qbig.scale : ℤ) : ℝ))) *
        normalizedL2SqOnSet (openCubeSet Qbig) (fun x ↦ u.toFun x - c) :=
    mul_nonneg (mul_nonneg hlam0 hscale) hnorm
  have hraw :=
    (Classical.choose_spec (exists_concentricRootEnergy_le_caccioppoli d)).2
      A m u c hu
  dsimp only at hraw
  have hP0 : 0 ≤ productRootEnergyPrefactor d C E := by
    unfold productRootEnergyPrefactor
    positivity
  have hfinal := hraw.trans (mul_le_mul hpref' hinner hinner0 hP0)
  simpa only [C, Qbig, Q, B, productConcentricInnerH1,
    productRootEnergyPrefactor] using hfinal

/-- A local product-error cap bounds the two-scale inner coefficient energy
by the centered parent oscillation.  All dependence on the error cap is
displayed explicitly; the Caccioppoli constant itself depends only on `d`. -/
theorem exists_productConcentricRootEnergy_le_of_localErrorCap
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ProductConcentricRootEnergyBound d C := by
  exact ⟨productCaccioppoliConstant d, productCaccioppoliConstant_pos d,
    productConcentricRootEnergyBound d⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
