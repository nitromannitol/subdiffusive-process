/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCenteredForce
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryFlatComparatorPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanTransport
import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLp
import Homogenization.Book.Ch03.ABK26.FluxComparisonBridges

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

/-!
# The direct forcing half of the flat-comparator loop

The constant mode of the source is removed before energy testing.  The
resulting zero-trace scalar divergence problem is passed through the public
`p = 2` cube Calderón--Zygmund endpoint and scaled Dirichlet Poincaré.

PROVENANCE: this is the `v_g - v` energy leg in
`Algsuperdiff/Section4/Provider/ExcessDecay/ResidueRouteOneErrorWeighted.lean`,
specialized to the scalar GMC comparator.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]

private theorem boundaryNormalizedEuclideanL2_grad_le_of_centeredSolution
    (m : ℤ) {sigma : ℝ} (hsigma : 0 < sigma)
    (F : CubeEuclideanL2LpField (originCube d m) FiniteLpExponent.two)
    (w : H10Function (openCubeSet (originCube d m)))
    (hw : IsCenteredCubeH10ScalarDivergenceSolution m sigma w F.toLpTwo) :
    boundaryNormalizedEuclideanL2 (originCube d m) w.toH1Function.grad ≤
      sigma⁻¹ * boundaryNormalizedEuclideanL2 (originCube d m) F.toField := by
  have hcz := CubeCalderonZygmund.centeredCubeH10ScalarDivergence_cz_two
    m sigma F w hsigma hw
  have hfin : (centeredCubeDomain d m).normalizedEuclideanLpENorm
      FiniteLpExponent.two.exponent F.toField ≠ ∞ := by
    simpa [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, FiniteLpExponent.two_exponent,
      euclideanNorm_eq_norm_ofVec] using F.euclideanMemL2.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
    (ENNReal.ofReal_pos.mpr hsigma).ne') hfin) hcz
  simpa [boundaryNormalizedEuclideanL2, cubeLpNorm,
    BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm,
    centeredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    FiniteLpExponent.two_exponent, euclideanNorm_eq_norm_ofVec,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hsigma.le,
    ] using hreal

omit [NeZero d] in
private theorem exists_scaledCenteredDivergenceWitness
    (m : ℤ) {sigma s : ℝ} (hsigma : 0 < sigma)
    {v h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hg : Homogenization.Book.Ch03.ForceBesovRegularity (originCube d m) s g)
    (hv : Homogenization.Book.Ch03.ABK26.IsScalarForcedEquation
      (originCube d m) sigma v g)
    (hh : IsUnitWeaklyHarmonicOn (openCubeSet (originCube d m)) h)
    (hzero : Homogenization.Book.Ch03.ABK26.HasH10Difference
      (originCube d m) v h) :
    ∃ w : H10Function (openCubeSet (originCube d m)),
      w.toH1Function.toFun =ᵐ[volume.restrict (openCubeSet (originCube d m))]
        (fun x ↦ v.toFun x - h.toFun x) ∧
      Homogenization.CubeDirichletDivergenceProblem
        (originCube d m) w
        (fun x => sigma⁻¹ • cubeFluctuationVec (originCube d m) g x) := by
  obtain ⟨w, hw⟩ := hzero
  have hw' : w.toH1Function.toFun =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      (v - h).toFun := by
    simpa only [volumeMeasureOn, H1Function.sub_toFun] using hw
  have hwgrad : w.toH1Function.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      (v - h).grad :=
    Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
      (isOpen_openCubeSet (originCube d m)) hw'
  refine ⟨w, by simpa only [H1Function.sub_toFun] using hw', ?_⟩
  intro phi
  have hvphi := hv phi
  have hhphi := hh phi
  have hgradInt :
      ∫ x in openCubeSet (originCube d m),
          vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet (originCube d m),
          vecDot (v.grad x - h.grad x) (phi.toH1Function.grad x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [hwgrad] with x hx
    simpa only [H1Function.sub_grad, Pi.sub_apply] using congrArg
      (fun z => vecDot z (phi.toH1Function.grad x)) hx
  have hsplit :
      ∫ x in openCubeSet (originCube d m),
          vecDot (v.grad x - h.grad x) (phi.toH1Function.grad x) ∂volume =
        (∫ x in openCubeSet (originCube d m),
          vecDot (v.grad x) (phi.toH1Function.grad x) ∂volume) -
        ∫ x in openCubeSet (originCube d m),
          vecDot (h.grad x) (phi.toH1Function.grad x) ∂volume := by
    have hvint := integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2
      phi.toH1Function.grad_memVectorL2
    have hhint := integrableOn_vecDot_of_memVectorL2 h.grad_memVectorL2
      phi.toH1Function.grad_memVectorL2
    have hfun : (fun x => vecDot (v.grad x - h.grad x) (phi.toH1Function.grad x)) =
        fun x => vecDot (v.grad x) (phi.toH1Function.grad x) -
          vecDot (h.grad x) (phi.toH1Function.grad x) := by
      funext x
      simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
    rw [hfun, integral_sub hvint hhint]
  have hraw : sigma * ∫ x in openCubeSet (originCube d m),
        vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume =
      -∫ x in openCubeSet (originCube d m),
        vecDot (cubeFluctuationVec (originCube d m) g x)
          (phi.toH1Function.grad x) ∂volume := by
    have hcenter := integral_vecDot_sub_const_zeroTraceGrad_eq
      (U := openCubeSet (originCube d m))
      (by
        have hcube := memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure
          (originCube d m) hg.memLp
        simpa [MemVectorL2, volumeMeasureOn,
          volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hcube)
      phi (cubeAverageVec (originCube d m) g)
    rw [hgradInt, hsplit, hhphi, sub_zero]
    have hvphi' : sigma * ∫ x in openCubeSet (originCube d m),
          vecDot (v.grad x) (phi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d m),
          vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
      have hfun : (fun x => vecDot
          (matVecMul (scalarMatrix (d := d) sigma) (v.grad x))
          (phi.toH1Function.grad x)) = fun x =>
            sigma * vecDot (v.grad x) (phi.toH1Function.grad x) := by
        funext x
        rw [Homogenization.matVecMul_scalarMatrix, vecDot_smul_left]
      rw [hfun, integral_const_mul] at hvphi
      exact hvphi
    rw [hvphi']
    congr 1
    simpa only [cubeFluctuationVec_apply] using hcenter.symm
  have hsigmaInv : sigma⁻¹ * sigma = 1 := inv_mul_cancel₀ hsigma.ne'
  have hscaled :
      ∫ x in openCubeSet (originCube d m),
          vecDot (sigma⁻¹ • cubeFluctuationVec (originCube d m) g x)
            (phi.toH1Function.grad x) ∂volume =
        sigma⁻¹ * ∫ x in openCubeSet (originCube d m),
          vecDot (cubeFluctuationVec (originCube d m) g x)
            (phi.toH1Function.grad x) ∂volume := by
    simp only [vecDot_smul_left]
    rw [integral_const_mul]
  rw [hscaled]
  calc
    ∫ x in openCubeSet (originCube d m),
          vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume =
        sigma⁻¹ * (sigma * ∫ x in openCubeSet (originCube d m),
          vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) := by
      rw [← mul_assoc, hsigmaInv, one_mul]
    _ = sigma⁻¹ * (-∫ x in openCubeSet (originCube d m),
          vecDot (cubeFluctuationVec (originCube d m) g x)
            (phi.toH1Function.grad x) ∂volume) := by rw [hraw]
    _ = -(sigma⁻¹ * ∫ x in openCubeSet (originCube d m),
          vecDot (cubeFluctuationVec (originCube d m) g x)
            (phi.toH1Function.grad x) ∂volume) := by ring

private theorem cubeLpNorm_h10_le_boundaryGradient (m : ℤ)
    (w : H10Function (openCubeSet (originCube d m))) :
    cubeLpNorm (originCube d m) 2 w.toH1Function.toFun ≤
      unitDirichletPoincareConst d * (3 : ℝ) ^ m * (d : ℝ) *
        boundaryNormalizedEuclideanL2 (originCube d m) w.toH1Function.grad := by
  let W : Set (Vec d) := openCubeSet (originCube d m)
  have hraw := eLpNorm_le_dirichletPoincare_translatedCube
    (W := W) (j := m) (z := 0) (measurableSet_openCubeSet (originCube d m))
    (by
      intro x hx
      simpa [W, translatedCube, cube] using hx) w
  have hWpos : 0 < (volume W).toReal := by
    dsimp [W]
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d m)
  have hdiv := div_le_div_of_nonneg_right hraw
    (Real.sqrt_nonneg ((volume W).toReal))
  have hvalMem : MemLp w.toH1Function.toFun 2 (volume.restrict W) := w.toH1Function.memL2
  have hgradMem : MemLp (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) 2
      (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField w.toH1Function.grad_memVectorL2
  have hsum := sum_normalizedL2On_coord_le_dimension_mul_vector hgradMem
  have hvec : vectorNormalizedL2On W w.toH1Function.grad =
      boundaryNormalizedEuclideanL2 (originCube d m) w.toH1Function.grad := by
    rw [vectorNormalizedL2On]
    rw [show (fun x => euclideanNorm (w.toH1Function.grad x)) =
        fun x => ‖HilbertVec.ofVec (w.toH1Function.grad x)‖ by
      funext x
      exact euclideanNorm_eq_norm_ofVec _]
    rw [
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div
        hgradMem.norm]
    rw [show boundaryNormalizedEuclideanL2 (originCube d m) w.toH1Function.grad =
        (eLpNorm (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) 2
          (normalizedCubeMeasure (originCube d m))).toReal by rfl]
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simp only [ENNReal.toReal_mul, smul_eq_mul]
    rw [← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_nonneg _))]
    rw [volume_openCubeSet_toReal]
    rw [eLpNorm_norm]
    norm_num
    rw [Real.sqrt_eq_rpow, Real.inv_rpow (cubeVolume_nonneg _)]
    ring
  have hnormalized : cubeLpNorm (originCube d m) 2 w.toH1Function.toFun ≤
      unitDirichletPoincareConst d * (3 : ℝ) ^ m *
        ∑ i : Fin d, normalizedL2On W (fun x => w.toH1Function.grad x i) := by
    rw [← normalizedL2On_openCubeSet_eq_cubeLpNorm (originCube d m) hvalMem]
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div
      hvalMem]
    refine hdiv.trans_eq ?_
    rw [mul_div_assoc, Finset.sum_div]
    congr 2
    funext i
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div
      (w.toH1Function.gradMemL2 i)]
  calc
    _ ≤ unitDirichletPoincareConst d * (3 : ℝ) ^ m *
        ∑ i : Fin d, normalizedL2On W (fun x => w.toH1Function.grad x i) := hnormalized
    _ ≤ unitDirichletPoincareConst d * (3 : ℝ) ^ m *
        ((d : ℝ) * vectorNormalizedL2On W w.toH1Function.grad) := by
      exact mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (unitDirichletPoincareConst_nonneg d)
          (zpow_nonneg (by norm_num) _))
    _ = _ := by rw [hvec]; ring

/-- A scalar forced solution and the flat harmonic function with the same
trace differ by the centered source price.  This is the direct-forcing term
which accompanies the homogenization error in the manuscript comparison. -/
theorem cubeLpNorm_scalarForced_sub_unitHarmonic_le_positiveBesov
    (m : ℤ) {sigma s : ℝ}
    (hsigma : 0 < sigma)
    {v h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hg : Homogenization.Book.Ch03.ForceBesovRegularity (originCube d m) s g)
    (hv : Homogenization.Book.Ch03.ABK26.IsScalarForcedEquation
      (originCube d m) sigma v g)
    (hh : IsUnitWeaklyHarmonicOn (openCubeSet (originCube d m)) h)
    (hzero : Homogenization.Book.Ch03.ABK26.HasH10Difference
      (originCube d m) v h) :
    cubeLpNorm (originCube d m) 2 (fun x => v.toFun x - h.toFun x) ≤
      unitDirichletPoincareConst d * (3 : ℝ) ^ m * (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
            (originCube d m) s g) := by
  obtain ⟨w, hwval, hwraw⟩ :=
    exists_scaledCenteredDivergenceWitness m hsigma hg hv hh hzero
  let gc : Vec d → Vec d := cubeFluctuationVec (originCube d m) g
  have hgcReg := forceBesovRegularity_cubeFluctuationVec hg
  have hgcCube : MemVectorL2 (cubeSet (originCube d m)) gc :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure (originCube d m) hgcReg.memLp
  have hgcHilbertVol : MemLp (fun x => HilbertVec.ofVec (gc x)) 2
      (volume.restrict (cubeSet (originCube d m))) :=
    memHilbertVectorL2_hilbertifyVecField hgcCube
  have hgcHilbert : MemLp (fun x => HilbertVec.ofVec (gc x)) 2
      (normalizedCubeMeasure (originCube d m)) := by
    simpa only [normalizedCubeMeasure, cubeMeasure] using
      hgcHilbertVol.smul_measure ENNReal.ofReal_ne_top
  have hscaledHilbert : MemLp
      (fun x => HilbertVec.ofVec (sigma⁻¹ • gc x)) 2
      (normalizedCubeMeasure (originCube d m)) := by
    have hs := hgcHilbert.const_smul sigma⁻¹
    simpa only [Pi.smul_apply, map_smul] using hs
  let F : CubeEuclideanL2LpField (originCube d m) FiniteLpExponent.two := {
    toField := fun x => sigma⁻¹ • gc x
    euclideanMemLp := hscaledHilbert
    euclideanMemL2 := hscaledHilbert }
  have hwsol : IsCenteredCubeH10ScalarDivergenceSolution m 1 w F.toLpTwo := by
    exact Homogenization.Book.Ch03.ABK26.cubeDirichletDivergenceProblem_to_centeredCubeH10ScalarDivergenceSolution m hscaledHilbert hwraw
  have hwgrad := boundaryNormalizedEuclideanL2_grad_le_of_centeredSolution
    m one_pos F w hwsol
  have hFNorm : boundaryNormalizedEuclideanL2 (originCube d m) F.toField =
      sigma⁻¹ * boundaryNormalizedEuclideanL2 (originCube d m) gc := by
    dsimp [F]
    simp only [boundaryNormalizedEuclideanL2, cubeLpNorm]
    have hfun : (fun x => HilbertVec.ofVec (sigma⁻¹ • gc x)) =
        sigma⁻¹ • (fun x => HilbertVec.ofVec (gc x)) := by
      funext x
      simp
    rw [hfun, MeasureTheory.eLpNorm_const_smul]
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (inv_nonneg.mpr hsigma.le),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hsigma.le)]
  have hwPoin := cubeLpNorm_h10_le_boundaryGradient m w
  have hgcPrice := boundaryNormalizedEuclideanL2_cubeFluctuationVec_le hg
  have hwNorm : cubeLpNorm (originCube d m) 2
      (fun x => v.toFun x - h.toFun x) =
      cubeLpNorm (originCube d m) 2 w.toH1Function.toFun := by
    unfold cubeLpNorm
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_ae
    have hwsmul : (fun x => v.toFun x - h.toFun x) =ᵐ[
        ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
          volume.restrict (openCubeSet (originCube d m))]
        w.toH1Function.toFun :=
      Measure.ae_smul_measure hwval.symm _
    simpa only [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hwsmul
  rw [hwNorm]
  calc
    _ ≤ unitDirichletPoincareConst d * (3 : ℝ) ^ m * (d : ℝ) *
        boundaryNormalizedEuclideanL2 (originCube d m) w.toH1Function.grad := hwPoin
    _ ≤ unitDirichletPoincareConst d * (3 : ℝ) ^ m * (d : ℝ) *
        boundaryNormalizedEuclideanL2 (originCube d m) F.toField := by
      exact mul_le_mul_of_nonneg_left (by simpa using hwgrad)
        (mul_nonneg
          (mul_nonneg (unitDirichletPoincareConst_nonneg d)
            (zpow_nonneg (by norm_num) _)) (Nat.cast_nonneg d))
    _ = unitDirichletPoincareConst d * (3 : ℝ) ^ m * (d : ℝ) * sigma⁻¹ *
        boundaryNormalizedEuclideanL2 (originCube d m) gc := by rw [hFNorm]; ring
    _ ≤ unitDirichletPoincareConst d * (3 : ℝ) ^ m * (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
            (originCube d m) s g) := by
      exact mul_le_mul_of_nonneg_left hgcPrice
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (unitDirichletPoincareConst_nonneg d)
              (zpow_nonneg (by norm_num) _)) (Nat.cast_nonneg d))
          (inv_nonneg.mpr hsigma.le))

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
