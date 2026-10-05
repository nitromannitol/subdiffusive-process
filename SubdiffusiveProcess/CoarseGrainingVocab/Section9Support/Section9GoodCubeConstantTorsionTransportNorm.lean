module

public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.ContinuousDiscreteKBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionTransportCarrier
@[expose] public section

/-!
Exact normalized `L²` change of variables for physical torsion differences.
The first identity retains the full extended-real norm. The subsequent real
readouts use the actual Sobolev carriers and the positive amplitude `alpha`.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The full unit-cube norm equals the physical normalized norm times `alpha / R²`. -/
theorem goodCube_l2Size_torsionPullback_sub_eq
    {d : ℕ} {m : ℤ} {alpha : ℝ} (halpha : 0 < alpha)
    (e v : H10Function (openCubeSet (originCube d m))) :
    l2Size (originCube d 0) (fun x =>
        (goodCubeTorsionPullback alpha e).toH1Function.toFun x -
          (goodCubeTorsionPullback alpha v).toH1Function.toFun x) =
      ENNReal.ofReal (alpha / (centeredCubeScale m) ^ 2) *
        eLpNorm (fun x => e.toH1Function.toFun x - v.toH1Function.toFun x)
          2 (normalizedCubeMeasure (originCube d m)) := by
  have hcnn : 0 ≤ alpha / (centeredCubeScale m) ^ 2 :=
    div_nonneg halpha.le (sq_nonneg (centeredCubeScale m))
  have hmeas : AEStronglyMeasurable
      (fun x => e.toH1Function.toFun x - v.toH1Function.toFun x)
      (normalizedCubeMeasure (originCube d m)) := by
    have he := e.toH1Function.memL2_normalizedCubeMeasure.aestronglyMeasurable
    have hv := v.toH1Function.memL2_normalizedCubeMeasure.aestronglyMeasurable
    exact he.sub hv
  have hfmp : MeasurePreserving (centeredCubeDilation m)
      (normalizedCubeMeasure (originCube d 0)) (normalizedCubeMeasure (originCube d m)) := by
    have h := centeredCubeDilationMeasurePreserving (d := d) m
    simp only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] at h
    exact h
  have hmeas0 : volume.restrict (openCubeSet (originCube d 0))
      = normalizedCubeMeasure (originCube d 0) :=
    (normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet d).symm
  have hnorm : ‖(alpha / (centeredCubeScale m) ^ 2 : ℝ)‖ₑ
      = ENNReal.ofReal (alpha / (centeredCubeScale m) ^ 2) := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hcnn]
  have key : eLpNorm
      (fun x => alpha / (centeredCubeScale m) ^ 2 *
        (e.toH1Function.toFun (centeredCubeScale m • x) -
          v.toH1Function.toFun (centeredCubeScale m • x)))
      2 (normalizedCubeMeasure (originCube d 0)) =
    ENNReal.ofReal (alpha / (centeredCubeScale m) ^ 2) *
      eLpNorm (fun x => e.toH1Function.toFun x - v.toH1Function.toFun x)
        2 (normalizedCubeMeasure (originCube d m)) := by
    have hfun : (fun x => alpha / (centeredCubeScale m) ^ 2 *
        (e.toH1Function.toFun (centeredCubeScale m • x) -
          v.toH1Function.toFun (centeredCubeScale m • x)))
        = (alpha / (centeredCubeScale m) ^ 2) •
          ((fun x => e.toH1Function.toFun x - v.toH1Function.toFun x) ∘
            centeredCubeDilation m) := by
      funext x
      simp [centeredCubeDilation, Pi.smul_apply, Function.comp_apply]
    rw [hfun, eLpNorm_const_smul, hnorm,
      eLpNorm_comp_measurePreserving hmeas hfmp]
  calc l2Size (originCube d 0) (fun x =>
        (goodCubeTorsionPullback alpha e).toH1Function.toFun x -
          (goodCubeTorsionPullback alpha v).toH1Function.toFun x)
      = eLpNorm (fun x => alpha / (centeredCubeScale m) ^ 2 *
          (e.toH1Function.toFun (centeredCubeScale m • x) -
            v.toH1Function.toFun (centeredCubeScale m • x)))
        2 (normalizedCubeMeasure (originCube d 0)) := by
        simp only [l2Size, goodCubeTorsionPullback_toFun, mul_sub]
        rw [hmeas0]
    _ = ENNReal.ofReal (alpha / (centeredCubeScale m) ^ 2) *
          eLpNorm (fun x => e.toH1Function.toFun x - v.toH1Function.toFun x)
            2 (normalizedCubeMeasure (originCube d m)) := key

/-- Physical normalized `L²` discrepancy is `R² / alpha` times the unit discrepancy. -/
theorem goodCube_cubeLpNorm_eq_scaled_torsionPullback_l2Size
    {d : ℕ} {m : ℤ} {alpha : ℝ} (halpha : 0 < alpha)
    (e v : H10Function (openCubeSet (originCube d m))) :
    cubeLpNorm (originCube d m) 2
        (fun x => e.toH1Function.toFun x - v.toH1Function.toFun x) =
      (centeredCubeScale m) ^ 2 / alpha *
        (l2Size (originCube d 0) (fun x =>
          (goodCubeTorsionPullback alpha e).toH1Function.toFun x -
            (goodCubeTorsionPullback alpha v).toH1Function.toFun x)).toReal := by
  have hcnn : 0 ≤ alpha / (centeredCubeScale m) ^ 2 :=
    div_nonneg halpha.le (sq_nonneg (centeredCubeScale m))
  have hcancel : (centeredCubeScale m) ^ 2 / alpha * (alpha / (centeredCubeScale m) ^ 2) = 1 := by
    field_simp [halpha.ne', centeredCubeScale_ne_zero m]
  have h1 := goodCube_l2Size_torsionPullback_sub_eq halpha e v
  simp only [cubeLpNorm]
  rw [h1, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcnn, ← mul_assoc, hcancel, one_mul]

/-- A unit-cube discrepancy bound gives the physical bound at the torsion scale. -/
theorem goodCube_cubeLpNorm_le_of_torsionPullback_l2Size_le
    {d : ℕ} {m : ℤ} {alpha eps : ℝ} (halpha : 0 < alpha) (heps : 0 ≤ eps)
    (e v : H10Function (openCubeSet (originCube d m)))
    (hunit : l2Size (originCube d 0) (fun x =>
      (goodCubeTorsionPullback alpha e).toH1Function.toFun x -
        (goodCubeTorsionPullback alpha v).toH1Function.toFun x) ≤ ENNReal.ofReal eps) :
    cubeLpNorm (originCube d m) 2
        (fun x => e.toH1Function.toFun x - v.toH1Function.toFun x) ≤
      (centeredCubeScale m) ^ 2 / alpha * eps := by
  have h2 := goodCube_cubeLpNorm_eq_scaled_torsionPullback_l2Size halpha e v
  have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hunit
  rw [ENNReal.toReal_ofReal heps] at hmono
  rw [h2]
  exact mul_le_mul_of_nonneg_left hmono
    (div_nonneg (sq_nonneg (centeredCubeScale m)) halpha.le)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
