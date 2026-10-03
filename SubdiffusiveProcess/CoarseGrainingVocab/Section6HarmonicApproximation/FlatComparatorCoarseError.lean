module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DirichletPrebalance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FinalReadout
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeScaleTransport

@[expose] public section

/-!
# Coarse-graining readout for a flat comparator

This module isolates the error loop used in the harmonic-approximation
argument.  A physical centered-cube coarse-graining estimate is dilated to
the unit cube and read through the manuscript negative fractional dual.  The
result is the normalized scalar `L²` distance between the coefficient and
scalar comparison solutions.

PROVENANCE: this is the GMC carrier version of the coarse-error readout in
`Algsuperdiff/Section4/Provider/ExcessDecay/ResidueRouteOneErrorWeighted.lean`.
The proof uses the landed finite-`p` Chapter 3 endpoint rather than adding a
new weak-norm estimate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem ofReal_centeredCubeScale_rpow_neg
    (m : ℤ) (s : ℝ) :
    (ENNReal.ofReal (centeredCubeScale m)) ^ (-s) =
      ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) := by
  rw [ENNReal.ofReal_rpow_of_pos (centeredCubeScale_pos m)]
  congr 1
  simp only [centeredCubeScale]
  rw [← Real.rpow_intCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring



theorem cubeLpNorm_sub_le_spectral_of_physicalCoarseGraining
    [NeZero d] (m : ℤ) {alpha : ℝ} (halpha : 0 < alpha)
    (s : FractionalOrder)
    (u v : H1Function (openCubeSet (originCube d m)))
    (hzero : HasH10Difference (originCube d m) u v)
    (Fflux : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two)
    {B : ℝ}
    (hphysical :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            ENNReal.ofReal alpha *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeGradientDifferenceL2Field m u v) +
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two Fflux ≤
        ENNReal.ofReal B) :
    cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
      (dirichletSpectralReadoutConstant s d *
        ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ * B)).toReal := by
  obtain ⟨w, hw⟩ := hzero
  let R : ℝ := centeredCubeScale m
  let uv : H1Function (openCubeSet (originCube d m)) := u - v
  let wUnit : H10Function (openCubeSet (originCube d 0)) :=
    R • centeredCubeNormalizedPullback w
  let Fgrad := centeredCubeGradientDifferenceL2Field m u v
  let FgradUnit := scaledCenteredCubePullbackEuclideanL2Field m R Fgrad
  have hdualSum := unitPaperNegativeDualSum_le_of_physicalCoarseGraining
    m halpha s Fgrad Fflux hphysical
  have hdualGrad :
      paperNegativeFractionalDual (originCube d 0) s
          FiniteLpExponent.two FgradUnit ≤
        ENNReal.ofReal (R * alpha⁻¹ * B) := by
    exact le_trans (le_add_right le_rfl) (by simpa only [R, Fgrad, FgradUnit] using! hdualSum)
  have hwgrad :
      (unitH10GradientEuclideanL2Field wUnit).toField =ᵐ[
          normalizedCubeMeasure (originCube d 0)] FgradUnit.toField := by
    have hw' : w.toH1Function.toFun =ᵐ[
        volume.restrict (openCubeSet (originCube d m))] uv.toFun := by
      simpa only [volumeMeasureOn, uv, H1Function.sub_toFun] using! hw
    have hgradVol : w.toH1Function.grad =ᵐ[
        volume.restrict (openCubeSet (originCube d m))] uv.grad :=
      H1Function.grad_ae_eq_of_toFun_ae_eq
        (isOpen_openCubeSet (originCube d m)) hw'
    have hgradNorm : w.toH1Function.grad =ᵐ[
        normalizedCubeMeasure (originCube d m)] fun x => u.grad x - v.grad x := by
      have hsmul := Measure.ae_smul_measure hgradVol
        (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹))
      simpa only [normalizedCubeMeasure, cubeMeasure,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
        uv, H1Function.sub_grad] using! hsmul
    have hgradPull :=
      (centeredCubeDilationMeasurePreserving (d := d) m).quasiMeasurePreserving.ae_eq
        (by simpa only [centeredCubeDomain,
          cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
          using hgradNorm)
    have hgradPull' :
        w.toH1Function.grad ∘ centeredCubeDilation m =ᵐ[
          normalizedCubeMeasure (originCube d 0)]
            (fun x => u.grad x - v.grad x) ∘ centeredCubeDilation m := by
      simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using hgradPull
    filter_upwards [hgradPull'] with x hx
    rw [unitH10GradientEuclideanL2Field_toField,
      scaledCenteredCubePullbackEuclideanL2Field_toField]
    change (R • (centeredCubeNormalizedPullback w).toH1Function).grad x =
      R • Fgrad.toField (centeredCubeScale m • x)
    rw [H1Function.smul_grad]
    change R • (centeredCubeNormalizedPullback w).toH1Function.grad x =
      R • Fgrad.toField (centeredCubeScale m • x)
    rw [centeredCubeNormalizedPullback_grad]
    change R • w.toH1Function.grad (centeredCubeScale m • x) =
      R • (u.grad (centeredCubeScale m • x) - v.grad (centeredCubeScale m • x))
    exact congrArg (fun z : Vec d => R • z) (by simpa only [Function.comp_apply] using! hx)
  have hdualEq :
      paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (unitH10GradientEuclideanL2Field wUnit) =
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          FgradUnit :=
    paperNegativeFractionalDual_congr_ae s FiniteLpExponent.two _ _ hwgrad
  have hspectral := l2Size_le_paperNegativeFractionalDual_gradient s wUnit
  rw [hdualEq] at hspectral
  have hunit : l2Size (originCube d 0) wUnit.toH1Function.toFun ≤
      dirichletSpectralReadoutConstant s d *
        ENNReal.ofReal (R * alpha⁻¹ * B) :=
    hspectral.trans (mul_le_mul_right hdualGrad _)
  have hwNorm : w.toH1Function.toFun =ᵐ[
      normalizedCubeMeasure (originCube d m)] fun x => u.toFun x - v.toFun x := by
    have hsmul := Measure.ae_smul_measure hw
      (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹))
    simpa only [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
      volumeMeasureOn] using! hsmul
  have hwPull :=
    (centeredCubeDilationMeasurePreserving (d := d) m).quasiMeasurePreserving.ae_eq
      (by simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using hwNorm)
  have hwUnitVal : wUnit.toH1Function.toFun =ᵐ[
      normalizedCubeMeasure (originCube d 0)]
        (fun x => u.toFun x - v.toFun x) ∘ centeredCubeDilation m := by
    have hwPull' :
        w.toH1Function.toFun ∘ centeredCubeDilation m =ᵐ[
          normalizedCubeMeasure (originCube d 0)]
            (fun x => u.toFun x - v.toFun x) ∘ centeredCubeDilation m := by
      simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using hwPull
    filter_upwards [hwPull'] with x hx
    change (R • (centeredCubeNormalizedPullback w).toH1Function).toFun x = _
    rw [H1Function.smul_toFun]
    change R * (centeredCubeNormalizedPullback w).toH1Function.toFun x = _
    rw [centeredCubeNormalizedPullback_apply]
    rw [show R = centeredCubeScale m by rfl, ← mul_assoc,
      mul_inv_cancel₀ (centeredCubeScale_ne_zero m), one_mul]
    simpa only [Function.comp_apply, centeredCubeDilation] using! hx
  have huvMem : MemLp (fun x => u.toFun x - v.toFun x) 2
      (normalizedCubeMeasure (originCube d m)) :=
    u.memL2_normalizedCubeMeasure.sub v.memL2_normalizedCubeMeasure
  have huvMem' : MemLp (fun x => u.toFun x - v.toFun x) 2
      (centeredCubeDomain d m).normalizedVolume := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      using huvMem
  have hcomp := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
    huvMem'.aestronglyMeasurable
    (centeredCubeDilationMeasurePreserving (d := d) m)
  have hnorm :
      l2Size (originCube d 0) wUnit.toH1Function.toFun =
        eLpNorm (fun x => u.toFun x - v.toFun x) 2
          (normalizedCubeMeasure (originCube d m)) := by
    unfold l2Size
    have hmeasure : normalizedCubeMeasure (originCube d 0) =
        volume.restrict (openCubeSet (originCube d 0)) := by
      simpa only [volumeMeasureOn] using!
        normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet d
    rw [← hmeasure]
    calc
      eLpNorm wUnit.toH1Function.toFun 2
          (normalizedCubeMeasure (originCube d 0)) =
        eLpNorm ((fun x => u.toFun x - v.toFun x) ∘ centeredCubeDilation m) 2
          (normalizedCubeMeasure (originCube d 0)) := eLpNorm_congr_ae hwUnitVal
      _ = eLpNorm (fun x => u.toFun x - v.toFun x) 2
          (normalizedCubeMeasure (originCube d m)) := by
        simpa only [centeredCubeDomain,
          cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
          using hcomp
  unfold cubeLpNorm
  rw [← hnorm]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top
      (dirichletSpectralReadoutConstant_lt_top s d).ne
      ENNReal.ofReal_ne_top) hunit

/-- The finite-`p` coarse-graining theorem followed by the preceding scalar
readout.  Its four numerical slots are deliberately identical to
`exists_generalCoarseGraining_two_le_dirichletRHS`, so local-error and energy
providers can be composed without another normalization layer. -/
theorem exists_cubeLpNorm_sub_le_dirichletCoarseGrainingRHS
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℤ), ∀ hnm : n < m,
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
        ∀ (alpha s s1 s2 : ℝ), 0 < alpha →
          ∀ hs1pos : 0 < s1, ∀ hs1s : s1 < s,
          ∀ hss2 : s < s2, ∀ hs2one : s2 < 1,
          ∀ (hs : FractionalOrder), hs.1 = s →
          ∀ (hs2 : FractionalOrder), hs2.1 = s2 →
          ∀ g : CubeEuclideanWspField (originCube d m) hs2
              FiniteLpExponent.two,
          ∀ u v : H1Function (openCubeSet (originCube d m)),
            IsForcedEquation (originCube d m) (a.coeffOn (originCube d m)) u
                g.toField →
            IsScalarForcedEquation (originCube d m) alpha v g.toField →
            HasH10Difference (originCube d m) u v →
          ∀ E1 E2 S D : ℝ, 0 ≤ E1 → 0 ≤ E2 → 0 ≤ S → 0 ≤ D →
            paperHomogenizationError (originCube d m) n s1
                .infinity (.finite 1) a alpha ≤ ENNReal.ofReal E1 →
            paperHomogenizationError (originCube d m) n (s1 / 2)
                .infinity (.finite 2) a alpha ≤ ENNReal.ofReal E2 →
            weightedLocalSymmetricEnergyLp (originCube d m) n
                (by simpa [originCube] using! hnm.le) (a.coeffOn (originCube d m)) u
                ⟨s1, hs1pos, by linarith⟩ hs FiniteLpExponent.two ≤
              ENNReal.ofReal S →
            paperFractionalSeminorm (originCube d m) hs2
                FiniteLpExponent.two g.toField ≤ ENNReal.ofReal D →
            cubeLpNorm (originCube d m) 2
                (fun x => u.toFun x - v.toFun x) ≤
              (dirichletSpectralReadoutConstant hs d *
                ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ *
                  dirichletCoarseGrainingRHS C alpha s s2 E1 E2 S D n)).toReal := by
  obtain ⟨C, hC, hcg⟩ := exists_generalCoarseGraining_two_le_dirichletRHS d hd
  refine ⟨C, hC, ?_⟩
  intro m n hnm a ha alpha s s1 s2 halpha hs1pos hs1s hss2 hs2one
    hs hhs hs2 hhs2 g u v hu hv huv E1 E2 S D hE10 hE20 hS0 hD0
    hE1 hE2 hS hD
  have hphysical := hcg m n hnm a ha alpha s s1 s2 halpha hs1pos hs1s
    hss2 hs2one hs hhs hs2 hhs2 g u v hu hv huv
    E1 E2 S D hE10 hE20 hS0 hD0 hE1 hE2 hS hD
  have hphysical' :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-hs.1) * ENNReal.ofReal alpha *
            paperNegativeFractionalDual (originCube d m) hs
              FiniteLpExponent.two (centeredCubeGradientDifferenceL2Field m u v) +
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-hs.1) *
            paperNegativeFractionalDual (originCube d m) hs
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field m
                (a.coeffOn (originCube d m)) alpha u v) ≤
        ENNReal.ofReal (dirichletCoarseGrainingRHS C alpha s s2 E1 E2 S D n) := by
    rw [hhs, ofReal_centeredCubeScale_rpow_neg]
    simpa only [ENNReal.ofReal_mul
      (p := Real.rpow 3 (-s * (m : ℝ))) (q := alpha)
      (Real.rpow_nonneg (by norm_num) _)] using! hphysical
  exact cubeLpNorm_sub_le_spectral_of_physicalCoarseGraining m halpha hs u v huv
    (centeredCubeFluxDifferenceL2Field m (a.coeffOn (originCube d m)) alpha u v)
    hphysical'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
