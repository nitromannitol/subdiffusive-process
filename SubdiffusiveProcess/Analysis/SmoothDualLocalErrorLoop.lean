module

public import SubdiffusiveProcess.Analysis.UniformSmoothDualReadout
public import SubdiffusiveProcess.Analysis.SmoothDualCoarseGraining
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorSharpReadout

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.UniformSmoothReadout

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section

/-! ### Smooth-dual pairing with a smooth test -/

/-- A smooth test, packaged as a fractional Sobolev field with its `L²`
certificate. -/
noncomputable def aux_smoothTestWspL2Field {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) : CubeEuclideanWspL2Field Q s p where
  toCubeEuclideanWspField := h.toCubeEuclideanWspField
  euclideanMemL2 := h.euclideanMemLp_two

/-- The smooth pairing is bounded by the smooth dual times the full norm of
the test. -/
theorem aux_ofReal_abs_smoothPairing_le {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p.conjugate) :
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
      cubeEuclideanNegativeWspSmoothDualENorm Q s p F *
        cubeEuclideanWspFullENorm Q s p.conjugate h.toField :=
  ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le F
    (aux_smoothTestWspL2Field h)

/-- The smooth negative dual depends only on the almost-everywhere class of
its field. -/
theorem aux_smoothDual_congr_ae {d : ℕ} {Q : TriadicCube d}
    (s : FractionalOrder) (p : FiniteLpExponent)
    (F G : CubeEuclideanLpField Q FiniteLpExponent.two)
    (hFG : F.toField =ᵐ[normalizedCubeMeasure Q] G.toField) :
    cubeEuclideanNegativeWspSmoothDualENorm Q s p F =
      cubeEuclideanNegativeWspSmoothDualENorm Q s p G := by
  unfold cubeEuclideanNegativeWspSmoothDualENorm
  apply iSup_congr
  intro h
  have hpair : cubeEuclideanNormalizedSmoothPairing F h.1 =
      cubeEuclideanNormalizedSmoothPairing G h.1 := by
    unfold cubeEuclideanNormalizedSmoothPairing
    apply integral_congr_ae
    filter_upwards [hFG] with x hx
    rw [hx]
  rw [hpair]

/-! ### Physical-to-unit transport of the smooth dual -/

/-- Inverse centered dilation of a unit-cube smooth test. -/
noncomputable def aux_inverseDilationSmoothTest {d : ℕ} (m : ℤ)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (h : CubeEuclideanWspSmoothTest (originCube d 0) s p) :
    CubeEuclideanWspSmoothTest (originCube d m) s p where
  toField := fun y ↦ h.toField ((centeredCubeScale m)⁻¹ • y)
  contDiff := h.contDiff.comp (contDiff_const_smul (centeredCubeScale m)⁻¹)

/-- The library full norm scales by exactly `(3^m)^(-s)` under the inverse
centered dilation. -/
theorem aux_fullENorm_inverseDilationSmoothTest {d : ℕ} (m : ℤ)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (h : CubeEuclideanWspSmoothTest (originCube d 0) s p) :
    cubeEuclideanWspFullENorm (originCube d m) s p
        (aux_inverseDilationSmoothTest m s p h).toField =
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        cubeEuclideanWspFullENorm (originCube d 0) s p h.toField := by
  have hcube : Book.Ch02.dilateCube m (originCube d 0) = originCube d m := by
    simp [Book.Ch02.dilateCube, originCube]
  have hpull : (fun x ↦
      (aux_inverseDilationSmoothTest m s p h).toField
        (Book.Ch02.dilateVec m x)) = h.toField := by
    funext x
    simp only [aux_inverseDilationSmoothTest, Book.Ch02.dilateVec, centeredCubeScale,
      Book.Ch02.triadicDilationFactor, smul_smul]
    rw [inv_mul_cancel₀ (zpow_ne_zero m (by norm_num : (3 : ℝ) ≠ 0)), one_smul]
  have hfull := cubeEuclideanWspFullENorm_dilate m (originCube d 0) s p
    (aux_inverseDilationSmoothTest m s p h).toField
  rw [hcube, hpull] at hfull
  rw [hfull]
  simp only [centeredCubeScale, Book.Ch02.triadicDilationFactor]

theorem aux_pairing_scaledCenteredCubePullback {d : ℕ} (m : ℤ) (c : ℝ)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest (originCube d 0) s p) :
    cubeEuclideanNormalizedSmoothPairing
        (scaledCenteredCubePullbackEuclideanL2Field m c F) h =
      c * cubeEuclideanNormalizedSmoothPairing F
        (aux_inverseDilationSmoothTest m s p h) := by
  let e : Vec d ≃ᵐ Vec d :=
    MeasurableEquiv.smul₀ (centeredCubeScale m) (centeredCubeScale_ne_zero m)
  have hi := (centeredCubeDilationMeasurePreserving (d := d) m).integral_comp
    e.measurableEmbedding
    (fun y ↦ vecDot (F.toField y)
      ((aux_inverseDilationSmoothTest m s p h).toField y))
  have hi' :
      (∫ x, vecDot (F.toField (centeredCubeDilation m x))
          ((aux_inverseDilationSmoothTest m s p h).toField
            (centeredCubeDilation m x)) ∂normalizedCubeMeasure (originCube d 0)) =
        ∫ y, vecDot (F.toField y)
          ((aux_inverseDilationSmoothTest m s p h).toField y)
            ∂normalizedCubeMeasure (originCube d m) := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using! hi
  unfold cubeEuclideanNormalizedSmoothPairing
  rw [← hi']
  simp only [scaledCenteredCubePullbackEuclideanL2Field_toField,
    centeredCubeDilation, aux_inverseDilationSmoothTest,
    smul_smul, inv_mul_cancel₀ (centeredCubeScale_ne_zero m), one_smul,
    vecDot_smul_left]
  exact integral_const_mul c _

/-- Smooth-dual scaling for an amplitude-weighted physical-to-unit pullback. -/
theorem aux_smoothDual_scaledCenteredCubePullback_le {d : ℕ} (m : ℤ) (c : ℝ)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two) :
    cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s p
        (scaledCenteredCubePullbackEuclideanL2Field m c F) ≤
      ‖c‖ₑ * (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p F := by
  rw [cubeEuclideanNegativeWspSmoothDualENorm]
  refine iSup_le fun h ↦ ?_
  let A : ℝ≥0∞ := (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1)
  let H := aux_inverseDilationSmoothTest m s p.conjugate h.1
  let DP := cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p F
  have hfullH : cubeEuclideanWspFullENorm (originCube d m) s p.conjugate H.toField =
      A * cubeEuclideanWspFullENorm (originCube d 0) s p.conjugate h.1.toField :=
    aux_fullENorm_inverseDilationSmoothTest m s p.conjugate h.1
  have hbound := aux_ofReal_abs_smoothPairing_le F H
  rw [hfullH] at hbound
  rw [aux_pairing_scaledCenteredCubePullback, abs_mul,
    ENNReal.ofReal_mul (abs_nonneg c), ← Real.enorm_eq_ofReal_abs]
  calc
    ‖c‖ₑ * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F H| ≤
        ‖c‖ₑ * (DP * (A *
          cubeEuclideanWspFullENorm (originCube d 0) s p.conjugate h.1.toField)) := by
      gcongr
    _ ≤ ‖c‖ₑ * (DP * (A * 1)) := by
      gcongr
      exact h.2
    _ = ‖c‖ₑ * A * DP := by ring

/-- Smooth-dual version of
`unitPaperNegativeDualSum_le_of_physicalCoarseGraining`. -/
theorem aux_unitSmoothDualSum_le_of_physicalCoarseGraining
    {d : ℕ} (m : ℤ) {alpha : ℝ} (halpha : 0 < alpha)
    (s : FractionalOrder)
    (Fgrad Fflux : CubeEuclideanLpField
      (originCube d m) FiniteLpExponent.two)
    {B : ℝ}
    (hphysical :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            ENNReal.ofReal alpha *
            cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
              FiniteLpExponent.two Fgrad +
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
              FiniteLpExponent.two Fflux ≤
        ENNReal.ofReal B) :
    cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s
          FiniteLpExponent.two
          (scaledCenteredCubePullbackEuclideanL2Field m
            (centeredCubeScale m) Fgrad) +
        cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s
          FiniteLpExponent.two
          (scaledCenteredCubePullbackEuclideanL2Field m
            (centeredCubeScale m * alpha⁻¹) Fflux) ≤
      ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ * B) := by
  let R : ℝ := centeredCubeScale m
  let A : ℝ≥0∞ := (ENNReal.ofReal R) ^ (-s.1)
  let K : ℝ≥0∞ := ENNReal.ofReal (R * alpha⁻¹)
  let Dg : ℝ≥0∞ := cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
    FiniteLpExponent.two Fgrad
  let Df : ℝ≥0∞ := cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
    FiniteLpExponent.two Fflux
  have hR : 0 < R := centeredCubeScale_pos m
  have hKreal : 0 ≤ R * alpha⁻¹ := mul_nonneg hR.le (inv_nonneg.mpr halpha.le)
  have hKR : K * ENNReal.ofReal alpha = ENNReal.ofReal R := by
    dsimp only [K]
    rw [← ENNReal.ofReal_mul hKreal]
    congr 1
    field_simp [halpha.ne']
  have hRnorm : ‖R‖ₑ = ENNReal.ofReal R := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos hR]
  have hKnorm : ‖R * alpha⁻¹‖ₑ = K := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hKreal]
  have hg := aux_smoothDual_scaledCenteredCubePullback_le
    m R s FiniteLpExponent.two Fgrad
  have hf := aux_smoothDual_scaledCenteredCubePullback_le
    m (R * alpha⁻¹) s FiniteLpExponent.two Fflux
  change A * ENNReal.ofReal alpha * Dg + A * Df ≤ ENNReal.ofReal B at hphysical
  change
    cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s FiniteLpExponent.two
          (scaledCenteredCubePullbackEuclideanL2Field m R Fgrad) +
        cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s FiniteLpExponent.two
          (scaledCenteredCubePullbackEuclideanL2Field m (R * alpha⁻¹) Fflux) ≤
      ENNReal.ofReal (R * alpha⁻¹ * B)
  calc
    _ ≤ ‖R‖ₑ * A * Dg + ‖R * alpha⁻¹‖ₑ * A * Df :=
      add_le_add hg hf
    _ = K * (A * ENNReal.ofReal alpha * Dg + A * Df) := by
      rw [hRnorm, hKnorm, ← hKR]
      ring
    _ ≤ K * ENNReal.ofReal B := by gcongr
    _ = ENNReal.ofReal (R * alpha⁻¹ * B) := by
      dsimp only [K]
      rw [ENNReal.ofReal_mul hKreal]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.UniformSmoothReadout


namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualScratch

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

/-- Smooth-dual version of the sharp physical-cube readout: a physical
centered-cube smooth-dual coarse-graining bound gives the `L²` difference with
the dimension-only constant `uniformSmoothDualReadoutConstant d` on `s ≤ 1/4`. -/
theorem cubeLpNorm_sub_le_uniformSmoothSpectral_of_physicalCoarseGraining
    {d : ℕ} [NeZero d] (m : ℤ) {alpha : ℝ} (halpha : 0 < alpha)
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4)
    (u v : H1Function (openCubeSet (originCube d m)))
    (hzero : HasH10Difference (originCube d m) u v)
    (Fflux : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two)
    {B : ℝ}
    (hphysical :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            ENNReal.ofReal alpha *
            cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeGradientDifferenceL2Field m u v) +
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
              FiniteLpExponent.two Fflux ≤
        ENNReal.ofReal B) :
    cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
      (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
        ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ * B)).toReal := by
  obtain ⟨w, hw⟩ := hzero
  let R : ℝ := centeredCubeScale m
  let uv : H1Function (openCubeSet (originCube d m)) := u - v
  let wUnit : H10Function (openCubeSet (originCube d 0)) :=
    R • centeredCubeNormalizedPullback w
  let Fgrad := centeredCubeGradientDifferenceL2Field m u v
  let FgradUnit := scaledCenteredCubePullbackEuclideanL2Field m R Fgrad
  have hdualSum := UniformSmoothReadout.aux_unitSmoothDualSum_le_of_physicalCoarseGraining
    m halpha s Fgrad Fflux hphysical
  have hdualGrad :
      cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s
          FiniteLpExponent.two FgradUnit ≤
        ENNReal.ofReal (R * alpha⁻¹ * B) := by
    exact le_trans (le_add_right le_rfl)
      (by simpa only [R, Fgrad, FgradUnit] using! hdualSum)
  have hwgrad :
      (Section6Dirichlet.unitH10GradientEuclideanL2Field wUnit).toField =ᵐ[
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
          using! hgradNorm)
    have hgradPull' :
        w.toH1Function.grad ∘ centeredCubeDilation m =ᵐ[
          normalizedCubeMeasure (originCube d 0)]
            (fun x => u.grad x - v.grad x) ∘ centeredCubeDilation m := by
      simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using! hgradPull
    filter_upwards [hgradPull'] with x hx
    rw [Section6Dirichlet.unitH10GradientEuclideanL2Field_toField,
      scaledCenteredCubePullbackEuclideanL2Field_toField]
    change (R • (centeredCubeNormalizedPullback w).toH1Function).grad x =
      R • Fgrad.toField (centeredCubeScale m • x)
    rw [H1Function.smul_grad]
    change R • (centeredCubeNormalizedPullback w).toH1Function.grad x =
      R • Fgrad.toField (centeredCubeScale m • x)
    rw [centeredCubeNormalizedPullback_grad]
    change R • w.toH1Function.grad (centeredCubeScale m • x) =
      R • (u.grad (centeredCubeScale m • x) - v.grad (centeredCubeScale m • x))
    exact congrArg (fun z : Vec d => R • z)
      (by simpa only [Function.comp_apply] using! hx)
  have hdualEq :
      cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s FiniteLpExponent.two
          (Section6Dirichlet.unitH10GradientEuclideanL2Field wUnit) =
        cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s FiniteLpExponent.two
          FgradUnit :=
    UniformSmoothReadout.aux_smoothDual_congr_ae s FiniteLpExponent.two _ _ hwgrad
  have hspectral := UniformSmoothReadout.l2Size_le_uniformSmoothDualReadoutConstant_mul_smoothDual s hs wUnit
  rw [hdualEq] at hspectral
  have hunit : l2Size (originCube d 0) wUnit.toH1Function.toFun ≤
      UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
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
        using! hwNorm)
  have hwUnitVal : wUnit.toH1Function.toFun =ᵐ[
      normalizedCubeMeasure (originCube d 0)]
        (fun x => u.toFun x - v.toFun x) ∘ centeredCubeDilation m := by
    have hwPull' :
        w.toH1Function.toFun ∘ centeredCubeDilation m =ᵐ[
          normalizedCubeMeasure (originCube d 0)]
            (fun x => u.toFun x - v.toFun x) ∘ centeredCubeDilation m := by
      simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using! hwPull
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
      using! huvMem
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
          using! hcomp
  unfold cubeLpNorm
  rw [← hnorm]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (UniformSmoothReadout.uniformSmoothDualReadoutConstant_lt_top d).ne
      ENNReal.ofReal_ne_top) hunit

private theorem aux_ofReal_centeredCubeScale_rpow_neg (m : ℤ) (t : ℝ) :
    (ENNReal.ofReal (centeredCubeScale m)) ^ (-t) =
      ENNReal.ofReal (Real.rpow 3 (-t * (m : ℝ))) := by
  rw [ENNReal.ofReal_rpow_of_pos (centeredCubeScale_pos m)]
  congr 1
  simp only [centeredCubeScale]
  rw [← Real.rpow_intCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- Smooth-dual local error loop: the finite-`p` coarse-graining endpoint at
`p = 2` in the smooth dual, followed by the uniform smooth-dual readout.
Compared with
`Section6HarmonicApproximation.exists_cubeLpNorm_sub_le_of_localCoarseGrainingLpRHS`,
the hypothesis carries no factor `(ofReal s)^(-1/2)` and the readout constant
is dimension-only; the corridor `s ≤ 1/4` is the readout's. -/
theorem exists_cubeLpNorm_sub_le_of_localCoarseGrainingLpRHS_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m n : ℤ) (hnm : n < m)
        (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 → s.1 ≤ 1 / 4 →
      ∀ (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
        (sigma : ℝ) (hsigma : 0 < sigma)
        (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma v g →
        HasH10Difference (originCube d m) u v →
      ∀ B : ℝ, 0 ≤ B →
        localCoarseGrainingLpRHS C (originCube d m) n
            (by simpa [originCube] using! hnm.le) a sigma hsigma g u
              s1 s s2 FiniteLpExponent.two ≤ ENNReal.ofReal B →
        cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale m * sigma⁻¹ * B)).toReal := by
  obtain ⟨C, hCtop, hcg⟩ :=
    SubdiffusiveProcess.Providers.Section2.SmoothDualScratch.exists_generalCoarseGraining_smoothDual_libraryRHS
      d hd FiniteLpExponent.two (by norm_num)
  refine ⟨C, hCtop, ?_⟩
  intro m n hnm s1 s s2 hs1s hss2 hs a sigma hsigma g hg u v hu hv huv B _hB hRHS
  have hraw := hcg m n hnm s1 s s2 hs1s hss2 a sigma hsigma g hg u v hu hv huv
  have hphysical :
      ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) * ENNReal.ofReal sigma *
            cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
              FiniteLpExponent.two (centeredCubeGradientDifferenceL2Field m u v) +
          ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
            cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field m a sigma u v) ≤
        ENNReal.ofReal B := by
    have htail := hraw.trans hRHS
    simpa only [mul_add, mul_assoc] using! htail
  have hphysical' :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) * ENNReal.ofReal sigma *
            cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
              FiniteLpExponent.two (centeredCubeGradientDifferenceL2Field m u v) +
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field m a sigma u v) ≤
        ENNReal.ofReal B := by
    rw [aux_ofReal_centeredCubeScale_rpow_neg]
    exact hphysical
  exact cubeLpNorm_sub_le_uniformSmoothSpectral_of_physicalCoarseGraining m hsigma s hs
    u v huv (centeredCubeFluxDifferenceL2Field m a sigma u v) hphysical'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualScratch


namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.UniformSmoothReadout

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section

/-- Comparison of the two negative duals in the direction that costs no power
of `s`: the smooth dual is at most twice the paper dual. -/
theorem aux_smoothDual_le_two_mul_paperDual {d : ℕ} {Q : TriadicCube d}
    (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    cubeEuclideanNegativeWspSmoothDualENorm Q s p F ≤
      2 * paperNegativeFractionalDual Q s p F := by
  rw [cubeEuclideanNegativeWspSmoothDualENorm]
  refine iSup_le fun h ↦ ?_
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1| ≤
        2 * paperNegativeFractionalDual Q s p F *
          cubeEuclideanWspFullENorm Q s p.conjugate h.1.toField :=
      ofReal_abs_normalizedFieldPairing_le_two_mul_paperNegativeFractionalDual F
        (aux_smoothTestWspL2Field h.1)
    _ ≤ 2 * paperNegativeFractionalDual Q s p F * 1 := by
      gcongr
      exact h.2
    _ = 2 * paperNegativeFractionalDual Q s p F := mul_one _

/-- Corollary (consistency check): the uniform smooth-dual readout implies a
uniform paper-dual readout with constant `2 * uniformSmoothDualReadoutConstant d`. -/
theorem l2Size_le_two_mul_uniformSmoothDualReadoutConstant_mul_paperDual
    {d : ℕ} [NeZero d] (s : FractionalOrder) (hs : s.1 ≤ 1 / 4)
    (w : H10Function (openCubeSet (originCube d 0))) :
    l2Size (originCube d 0) w.toH1Function.toFun ≤
      2 * uniformSmoothDualReadoutConstant d *
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (unitH10GradientEuclideanL2Field w) := by
  calc
    l2Size (originCube d 0) w.toH1Function.toFun ≤
        uniformSmoothDualReadoutConstant d *
          cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s
            FiniteLpExponent.two (unitH10GradientEuclideanL2Field w) :=
      l2Size_le_uniformSmoothDualReadoutConstant_mul_smoothDual s hs w
    _ ≤ uniformSmoothDualReadoutConstant d *
          (2 * paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
            (unitH10GradientEuclideanL2Field w)) := by
      gcongr
      exact aux_smoothDual_le_two_mul_paperDual s FiniteLpExponent.two _
    _ = 2 * uniformSmoothDualReadoutConstant d *
          paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
            (unitH10GradientEuclideanL2Field w) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.UniformSmoothReadout
