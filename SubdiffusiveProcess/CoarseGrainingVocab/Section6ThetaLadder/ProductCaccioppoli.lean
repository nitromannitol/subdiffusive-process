import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductEnergyReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergy

/-!
# Theta-perturbed ladder: concentric product Caccioppoli

The sharp comparator runs two scales below the equation window.  On concentric
origin cubes, that inner cube is literally the Caccioppoli core.  This file
performs the coefficient-family restriction and reads the core estimate as the
root coefficient energy consumed by `ProductEnergyReadout`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Filter MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem publicIsForcedEquation_zero_of_abk26
    {Q : TriadicCube d} {A : Ch02.TriadicCoeffFamily d}
    {u : H1Function (openCubeSet Q)}
    (hu : Ch03.ABK26.IsForcedEquation Q (A.coeffOn Q) u (fun _ ↦ 0)) :
    IsForcedEquation Q A u (fun _ ↦ 0) := by
  intro phi
  have h := hu phi
  have hzero : (∫ x in openCubeSet Q,
      vecDot (0 : Vec d) (phi.toH1Function.grad x) ∂volume) = 0 := by
    simp only [vecDot_zero_left, integral_zero]
  rw [hzero, neg_zero] at h
  simpa only [Ch02.cubeDomain_coe, vecDot_zero_left, integral_zero] using h

/-- A two-scale inner root energy is controlled by the centered parent
oscillation for every coefficient family and every homogeneous solution. -/
theorem exists_concentricRootEnergy_le_caccioppoli (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Ch02.TriadicCoeffFamily d) (m : ℤ)
        (u : H1Function (openCubeSet (originCube d (m + 2)))) (c : ℝ),
      Ch03.ABK26.IsForcedEquation (originCube d (m + 2))
          (A.coeffOn (originCube d (m + 2))) u (fun _ ↦ 0) →
      let Qbig := originCube d (m + 2)
      let Q := originCube d m
      let hsub : openCubeSet Q ⊆ openCubeSet Qbig :=
        openCubeSet_originCube_subset_of_scale_le (by omega)
      let uQ := u.restrict (isOpen_openCubeSet Q) hsub
      cubeAverage Q
          (coefficientEnergyDensity (A.coeffOn Q).toCoeffField uQ.grad) ≤
        caccioppoliWithRHSPrefactor C Qbig A (1 / 2) (3 / 32) *
          (Ch02.lambdaS Qbig (3 / 32) A *
            Real.rpow (3 : ℝ) (-2 * (((Qbig.scale : ℤ) : ℝ))) *
            normalizedL2SqOnSet (openCubeSet Qbig)
              (fun x ↦ u.toFun x - c)) := by
  obtain ⟨C, hC, hmain⟩ := exists_interior_caccioppoli_quarter_subConst d
  refine ⟨C, hC, ?_⟩
  intro A m u c hu
  dsimp only
  let Qbig := originCube d (m + 2)
  let Q := originCube d m
  have hsub : openCubeSet Q ⊆ openCubeSet Qbig :=
    openCubeSet_originCube_subset_of_scale_le (by omega)
  let uQ : H1Function (openCubeSet Q) :=
    u.restrict (isOpen_openCubeSet Q) hsub
  have hpatch : openCubeAtScale (0 : Vec d) (Qbig.scale - 1) ⊆
      openCubeSet Qbig := by
    rw [show Qbig.scale - 1 = m + 1 by
      change (m + 2) - 1 = m + 1
      ring]
    rw [openCubeAtScale_zero_eq_openCubeSet_originCube]
    exact openCubeSet_originCube_subset_of_scale_le (by omega)
  have hsmall : openCubeAtScale (0 : Vec d) (Qbig.scale - 2) ⊆
      openCubeSet Qbig := by
    rw [show Qbig.scale - 2 = m by
      change (m + 2) - 2 = m
      ring]
    rw [openCubeAtScale_zero_eq_openCubeSet_originCube]
    exact hsub
  have hcore : caccioppoliCoreSet Qbig (0 : Vec d) = openCubeSet Q := by
    rw [caccioppoliCoreSet_eq_openCubeAtScale hsmall]
    rw [show Qbig.scale - 2 = m by
      change (m + 2) - 2 = m
      ring,
      openCubeAtScale_zero_eq_openCubeSet_originCube]
  have hloc := hmain u c (publicIsForcedEquation_zero_of_abk26 hu)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 3 / 32) (by norm_num : (3 / 32 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 2 : ℝ) + 3 / 32 < 1) hpatch
    (forceBesovRegularity_zero Qbig (2 * (3 / 32 : ℝ)))
  rw [hcore] at hloc
  have hrestrict : Ch02.CoeffOn.RestrictsTo
      (A.coeffOn Qbig) (A.coeffOn Q) := A.restrictsTo_of_subset hsub
  have henergy :
      localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q) uQ =
        localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Qbig) u := by
    unfold localizedCoeffEnergyValue normalizedSetAverage volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hrestrict] with x hx
    simp [uQ, H1Function.restrict, hx]
  rw [← henergy] at hloc
  change volumeAverage (openCubeSet Q)
    (coefficientEnergyDensity (A.coeffOn Q).toCoeffField uQ.grad) ≤ _ at hloc
  rw [volumeAverage_openCubeSet_eq_cubeAverage] at hloc
  have hzero : scaleNormalizedPositiveBesovVectorSeminormTwo Qbig
      (2 * (3 / 32 : ℝ)) (fun _ ↦ (0 : Vec d)) = 0 := by
    unfold scaleNormalizedPositiveBesovVectorSeminormTwo
    change cubeBesovPositiveVectorSeminormTwo Qbig (2 * (3 / 32 : ℝ))
      (0 : Vec d → Vec d) = 0
    rw [cubeBesovPositiveVectorSeminormTwo_zero]
  rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at hloc
  simpa only [Qbig, Q, uQ, hsub] using hloc

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
