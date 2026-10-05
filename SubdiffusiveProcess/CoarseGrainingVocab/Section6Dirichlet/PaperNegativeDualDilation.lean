module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DifferenceFields
public import SubdiffusiveProcess.CoarseGrainingVocab.PaperFractionalDualBridge
public import Homogenization.Sobolev.Fractional.EuclideanWspDilation

@[expose] public section

/-!
# Dilation of the manuscript negative fractional dual

This is the normalized-cube change of variables used before the final
Dirichlet parameter balance.  The pullback is from the physical centered
cube to the unit cube, with an additional deterministic amplitude.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- Pull a globally smooth unit-cube test back through the inverse centered
dilation, obtaining a globally smooth physical-cube test. -/
def inverseCenteredCubeDilationSmoothTest {d : ℕ} (m : ℤ)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (h : CubeEuclideanWspSmoothTest (originCube d 0) s p) :
    CubeEuclideanWspSmoothTest (originCube d m) s p where
  toField := fun y ↦ h.toField ((centeredCubeScale m)⁻¹ • y)
  contDiff := h.contDiff.comp (contDiff_const_smul (centeredCubeScale m)⁻¹)

@[simp] private theorem inverseCenteredCubeDilationSmoothTest_toField
    {d : ℕ} (m : ℤ) (s : FractionalOrder) (p : FiniteLpExponent)
    (h : CubeEuclideanWspSmoothTest (originCube d 0) s p) (y : Vec d) :
    (inverseCenteredCubeDilationSmoothTest m s p h).toField y =
      h.toField ((centeredCubeScale m)⁻¹ • y) :=
  rfl

/-- The additive positive manuscript norm has the exact physical scaling
factor under inverse dilation. -/
theorem paperFractionalFullNorm_inverseCenteredCubeDilation
    {d : ℕ} (m : ℤ) (s : FractionalOrder) (p : FiniteLpExponent)
    (h : CubeEuclideanWspSmoothTest (originCube d 0) s p) :
    paperFractionalFullNorm (originCube d m) s p
        (inverseCenteredCubeDilationSmoothTest m s p h).toField =
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        paperFractionalFullNorm (originCube d 0) s p h.toField := by
  have hcube : Book.Ch02.dilateCube m (originCube d 0) = originCube d m := by
    simp [Book.Ch02.dilateCube, originCube]
  have hpull : (fun x ↦
      (inverseCenteredCubeDilationSmoothTest m s p h).toField
        (Book.Ch02.dilateVec m x)) = h.toField := by
    funext x
    simp only [inverseCenteredCubeDilationSmoothTest_toField,
      Book.Ch02.dilateVec, centeredCubeScale,
      Book.Ch02.triadicDilationFactor, smul_smul]
    rw [inv_mul_cancel₀ (zpow_ne_zero m (by norm_num : (3 : ℝ) ≠ 0)), one_smul]
  have hsemi := cubeEuclideanWspESeminorm_dilate m (originCube d 0) s p
    (inverseCenteredCubeDilationSmoothTest m s p h).toField
  rw [hcube, hpull] at hsemi
  have hLp := cubeEuclideanNormalizedLpENorm_dilate m (originCube d 0) p
    (inverseCenteredCubeDilationSmoothTest m s p h).toField
  rw [hcube, hpull] at hLp
  simp only [paperFractionalFullNorm, paperFractionalSeminorm]
  rw [hsemi, hLp]
  simp only [centeredCubeScale, cubeScaleFactor_originCube,
    Book.Ch02.triadicDilationFactor]
  simp only [zpow_zero, ENNReal.ofReal_one, ENNReal.one_rpow, one_mul]
  ring

/-- Euclidean `L²` packaging of the amplitude-weighted centered pullback. -/
noncomputable def scaledCenteredCubePullbackEuclideanL2Field {d : ℕ}
    (m : ℤ) (c : ℝ)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two) :
    CubeEuclideanLpField (originCube d 0) FiniteLpExponent.two :=
  l2VectorFieldToCubeEuclideanL2Field (originCube d 0)
    (scaledCenteredCubePullbackL2VectorField m c F)

@[simp] theorem scaledCenteredCubePullbackEuclideanL2Field_toField
    {d : ℕ} (m : ℤ) (c : ℝ)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two)
    (x : Vec d) :
    (scaledCenteredCubePullbackEuclideanL2Field m c F).toField x =
      c • F.toField (centeredCubeScale m • x) :=
  rfl

private theorem normalizedPairing_scaledCenteredCubePullback
    {d : ℕ} (m : ℤ) (c : ℝ) (s : FractionalOrder)
    (p : FiniteLpExponent)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest (originCube d 0) s p) :
    cubeEuclideanNormalizedSmoothPairing
        (scaledCenteredCubePullbackEuclideanL2Field m c F) h =
      c * cubeEuclideanNormalizedSmoothPairing F
        (inverseCenteredCubeDilationSmoothTest m s p h) := by
  let e : Vec d ≃ᵐ Vec d :=
    MeasurableEquiv.smul₀ (centeredCubeScale m) (centeredCubeScale_ne_zero m)
  have he : (e : Vec d → Vec d) = centeredCubeDilation m := rfl
  have hi := (centeredCubeDilationMeasurePreserving (d := d) m).integral_comp
    e.measurableEmbedding
    (fun y ↦ vecDot (F.toField y)
      ((inverseCenteredCubeDilationSmoothTest m s p h).toField y))
  have hi' :
      (∫ x, vecDot (F.toField (centeredCubeDilation m x))
          ((inverseCenteredCubeDilationSmoothTest m s p h).toField
            (centeredCubeDilation m x)) ∂normalizedCubeMeasure (originCube d 0)) =
        ∫ y, vecDot (F.toField y)
          ((inverseCenteredCubeDilationSmoothTest m s p h).toField y)
            ∂normalizedCubeMeasure (originCube d m) := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using! hi
  unfold cubeEuclideanNormalizedSmoothPairing
  rw [← hi']
  simp only [scaledCenteredCubePullbackEuclideanL2Field_toField,
    centeredCubeDilation, inverseCenteredCubeDilationSmoothTest_toField,
    smul_smul, inv_mul_cancel₀ (centeredCubeScale_ne_zero m), one_smul,
    vecDot_smul_left]
  exact integral_const_mul c _

/-- Exact manuscript negative-dual scaling for an amplitude-weighted
physical-to-unit pullback. -/
theorem paperNegativeFractionalDual_scaledCenteredCubePullback_le
    {d : ℕ} (m : ℤ) (c : ℝ) (s : FractionalOrder)
    (p : FiniteLpExponent)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two) :
    paperNegativeFractionalDual (originCube d 0) s p
        (scaledCenteredCubePullbackEuclideanL2Field m c F) ≤
      ‖c‖ₑ * (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        paperNegativeFractionalDual (originCube d m) s p F := by
  rw [paperNegativeFractionalDual]
  refine iSup_le fun h ↦ ?_
  let N : ℝ≥0∞ := paperFractionalFullNorm (originCube d 0) s p.conjugate h.1.toField
  let A : ℝ≥0∞ := (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1)
  let C : ℝ≥0∞ := ‖c‖ₑ
  let H := inverseCenteredCubeDilationSmoothTest m s p.conjugate h.1
  let NP : ℝ≥0∞ := paperFractionalFullNorm (originCube d m) s p.conjugate H.toField
  let DP : ℝ≥0∞ := paperNegativeFractionalDual (originCube d m) s p F
  have hN0 : N ≠ 0 := h.2
  have hNtop : N ≠ ∞ := (paperFractionalFullNorm_lt_top_of_smooth h.1).ne
  have hA0 : A ≠ 0 := ne_of_gt (ENNReal.rpow_pos
    (ENNReal.ofReal_pos.mpr (centeredCubeScale_pos m)) ENNReal.ofReal_ne_top)
  have hAtop : A ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos m)) ENNReal.ofReal_ne_top
  have hNP : NP = A * N := by
    exact paperFractionalFullNorm_inverseCenteredCubeDilation m s p.conjugate h.1
  have hNP0 : NP ≠ 0 := by rw [hNP]; exact mul_ne_zero hA0 hN0
  have hNPtop : NP ≠ ∞ := by
    rw [hNP]
    exact ENNReal.mul_ne_top hAtop hNtop
  let hp : {g : CubeEuclideanWspSmoothTest (originCube d m) s p.conjugate //
      paperFractionalFullNorm (originCube d m) s p.conjugate g.1 ≠ 0} :=
    ⟨H, hNP0⟩
  have hratio :
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F H| / NP ≤ DP := by
    rw [show DP = paperNegativeFractionalDual (originCube d m) s p F by rfl,
      paperNegativeFractionalDual]
    exact le_iSup (fun g : {g : CubeEuclideanWspSmoothTest
        (originCube d m) s p.conjugate //
          paperFractionalFullNorm (originCube d m) s p.conjugate g.1 ≠ 0} ↦
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F g.1| /
        paperFractionalFullNorm (originCube d m) s p.conjugate g.1.toField) hp
  have hphysical :
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F H| ≤ DP * NP :=
    (ENNReal.div_le_iff hNP0 hNPtop).mp hratio
  have hpair :
      ENNReal.ofReal
          |cubeEuclideanNormalizedSmoothPairing
            (scaledCenteredCubePullbackEuclideanL2Field m c F) h.1| =
        C * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F H| := by
    rw [normalizedPairing_scaledCenteredCubePullback]
    calc
      ENNReal.ofReal |c * cubeEuclideanNormalizedSmoothPairing F H| =
          ENNReal.ofReal (|c| *
            |cubeEuclideanNormalizedSmoothPairing F H|) := by rw [abs_mul]
      _ = ENNReal.ofReal |c| *
          ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F H| :=
        ENNReal.ofReal_mul (abs_nonneg c)
      _ = C * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F H| := by
        rw [show C = ‖c‖ₑ by rfl, Real.enorm_eq_ofReal_abs]
  apply (ENNReal.div_le_iff hN0 hNtop).mpr
  rw [hpair]
  calc
    C * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F H| ≤
        C * (DP * NP) := mul_le_mul_right hphysical C
    _ = C * (DP * (A * N)) := by rw [hNP]
    _ = (C * A * DP) * N := by ring
    _ = (‖c‖ₑ * (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        paperNegativeFractionalDual (originCube d m) s p F) * N := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
