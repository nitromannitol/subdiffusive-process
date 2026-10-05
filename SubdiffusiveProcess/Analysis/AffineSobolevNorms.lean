module

public import SubdiffusiveProcess.Sobolev.NativeH1
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.CoarseGrainingVocab.Norms
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicCovariance
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.ContinuousDiscreteKBridge

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.AffineSobolevNorms

theorem nativeH1_axis {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    ∃ uH : Homogenization.H1Function
        (Homogenization.axisCube (fun i => z i - r / 2) r),
      uH.toFun = (fun x =>
          (u : SobolevData (centeredCube z r hr)).1 x) ∧
      ∀ x i, uH.grad x i =
        (u : SobolevData (centeredCube z r hr)).2 i x := by
  let w : SpatialCoordinates d := fun i => z i - r / 2
  have hset : Homogenization.axisCube w r =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi z hr]
    ext x
    simp [Homogenization.axisCube, w]
    constructor
    · intro hx i
      exact ⟨hx i |>.1, by linarith [hx i |>.2]⟩
    · intro hx i
      exact ⟨hx i |>.1, by linarith [hx i |>.2]⟩
  obtain ⟨uH, hfun, hgrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph u
  let uA : Homogenization.H1Function (Homogenization.axisCube w r) := hset.symm ▸ uH
  refine ⟨uA, ?_, ?_⟩
  · calc
      uA.toFun = uH.toFun := by
        exact Homogenization.H1Function.toFun_castDomain hset.symm uH
      _ = (fun x => (u : SobolevData (centeredCube z r hr)).1 x) := hfun
  · intro x i
    have hgradA : uA.grad =
        (fun x i => (u : SobolevData (centeredCube z r hr)).2 i x) := by
      calc
        uA.grad = uH.grad := Homogenization.H1Function.grad_castDomain hset.symm uH
        _ = _ := hgrad
    exact congrFun (congrFun hgradA x) i

theorem normalized_l2_rescaled_pullback {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : SobolevData (centeredCube z r hr))
    (uA : Homogenization.H1Function
      (Homogenization.axisCube (fun i => z i - r / 2) r))
    (hfun : uA.toFun = fun x => (u : SobolevData (centeredCube z r hr)).1 x)
    (v : Homogenization.H1Function
      (Homogenization.openCubeSet (Homogenization.originCube d 0)))
    (hv : ∀ x, v.toFun x = r⁻¹ *
      (u : SobolevData (centeredCube z r hr)).1 (fun j => z j + r * x j)) :
    ‖(u : SobolevData (centeredCube z r hr)).1‖ /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) =
      r * Homogenization.cubeLpNorm (Homogenization.originCube d 0)
        (2 : ℝ≥0∞) v.toFun := by
  let w : SpatialCoordinates d := fun i => z i - r / 2
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  have hset : Homogenization.axisCube w r =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi z hr]
    ext x
    simp [Homogenization.axisCube, w]
    constructor
    · intro hx i
      exact ⟨hx i |>.1, by linarith [hx i |>.2]⟩
    · intro hx i
      exact ⟨hx i |>.1, by linarith [hx i |>.2]⟩
  have hvolume : volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = r ^ d :=
    centeredCube_volume_real z hr
  have hnormPhysical : ‖(u : SobolevData (centeredCube z r hr)).1‖ =
      (MeasureTheory.eLpNorm (fun x =>
        (u : SobolevData (centeredCube z r hr)).1 x) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal := by
    rw [MeasureTheory.Lp.norm_def]
  have hphysicalA :
      MeasureTheory.eLpNorm (fun x =>
        (u : SobolevData (centeredCube z r hr)).1 x) 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) =
      MeasureTheory.eLpNorm uA.toFun 2 (volume.restrict (Homogenization.axisCube w r)) := by
    calc
      _ = MeasureTheory.eLpNorm uA.toFun 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
        MeasureTheory.eLpNorm_congr_ae
          (Filter.Eventually.of_forall fun x => (congrFun hfun x).symm)
      _ = MeasureTheory.eLpNorm uA.toFun 2 (volume.restrict (Homogenization.axisCube w r)) := by
        exact congrArg (fun μ => MeasureTheory.eLpNorm uA.toFun 2 μ)
          (congrArg (fun s : Set (SpatialCoordinates d) => volume.restrict s) hset.symm)
  have hscaleMeasure :
      MeasureTheory.eLpNorm uA.toFun 2
          (Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure w r) =
        (ENNReal.ofReal ((r ^ d)⁻¹)) ^ (1 / 2 : ℝ) *
          MeasureTheory.eLpNorm uA.toFun 2 (volume.restrict (Homogenization.axisCube w r)) := by
    rw [Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
      w r hr]
    rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero
      (c := ENNReal.ofReal ((r ^ d)⁻¹)) (by
        exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (pow_pos hr _)))]
    simp only [smul_eq_mul]
    congr 1
    norm_num
  have hscaleReal :
      (MeasureTheory.eLpNorm uA.toFun 2
        (Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure w r)).toReal =
        (Real.sqrt (r ^ d))⁻¹ *
          (MeasureTheory.eLpNorm uA.toFun 2
            (volume.restrict (Homogenization.axisCube w r))).toReal := by
    rw [hscaleMeasure]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.ofReal_rpow_of_nonneg
        (inv_nonneg.mpr (pow_pos hr d).le) (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg (inv_nonneg.mpr (pow_pos hr d).le) _)]
    rw [Real.sqrt_eq_rpow, Real.inv_rpow (pow_nonneg hr.le d) (1 / 2 : ℝ)]
  have hameas : MeasureTheory.AEStronglyMeasurable uA.toFun
      (Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure w r) := by
    rw [Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
      w r hr]
    exact uA.memL2.aestronglyMeasurable.smul_measure
      (ENNReal.ofReal ((r ^ d)⁻¹))
  have hcomp := Homogenization.CubeCalderonZygmund.eLpNorm_axisCubeAffine
      w r (2 : ℝ≥0∞) uA.toFun hameas
  have hcoord : ∀ x : SpatialCoordinates d,
      (fun j => z j + r * x j) =
        Homogenization.CubeCalderonZygmund.axisCubeAffine w r x := by
    intro x
    funext j
    simp [Homogenization.CubeCalderonZygmund.axisCubeAffine,
      Homogenization.CubeCalderonZygmund.axisCubeCenter, w]
    ring
  have hvA : ∀ x, v.toFun x = r⁻¹ *
      uA.toFun (Homogenization.CubeCalderonZygmund.axisCubeAffine w r x) := by
    intro x
    rw [hv, hfun]
    exact congrArg (fun y => r⁻¹ *
      (u : SobolevData (centeredCube z r hr)).1 y) (hcoord x)
  have hunitMeasure :=
    Homogenization.normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet d
  have hunitNorm :
      MeasureTheory.eLpNorm v.toFun 2 (Homogenization.normalizedCubeMeasure Q) =
        ENNReal.ofReal (r⁻¹) *
          MeasureTheory.eLpNorm uA.toFun 2
            (Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure w r) := by
    rw [hunitMeasure]
    calc
      MeasureTheory.eLpNorm v.toFun 2
          (volume.restrict (Homogenization.openCubeSet Q)) =
        MeasureTheory.eLpNorm (fun x => r⁻¹ *
          uA.toFun (Homogenization.CubeCalderonZygmund.axisCubeAffine w r x)) 2
          (volume.restrict (Homogenization.openCubeSet Q)) := by
            apply MeasureTheory.eLpNorm_congr_ae
            exact Filter.Eventually.of_forall hvA
      _ = ENNReal.ofReal (r⁻¹) *
          MeasureTheory.eLpNorm
            (fun x => uA.toFun
              (Homogenization.CubeCalderonZygmund.axisCubeAffine w r x)) 2
            (volume.restrict (Homogenization.openCubeSet Q)) := by
              have hsmul : (fun x => r⁻¹ *
                  uA.toFun (Homogenization.CubeCalderonZygmund.axisCubeAffine w r x)) =
                  r⁻¹ • (fun x => uA.toFun
                    (Homogenization.CubeCalderonZygmund.axisCubeAffine w r x)) := by
                funext x
                rfl
              rw [hsmul, MeasureTheory.eLpNorm_const_smul]
              rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hr)]
      _ = _ := by rw [hcomp]
  have hunitReal :
      Homogenization.cubeLpNorm Q 2 v.toFun = r⁻¹ *
        (MeasureTheory.eLpNorm uA.toFun 2
          (Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure w r)).toReal := by
    rw [Homogenization.cubeLpNorm, hunitNorm]
    rw [ENNReal.toReal_mul]
    simp [ENNReal.toReal_ofReal, le_of_lt (inv_pos.mpr hr)]
  rw [hnormPhysical, hphysicalA, hvolume, hunitReal, hscaleReal]
  have hrsqrt : Real.sqrt (r ^ d) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (pow_pos hr _))
  field_simp [hrsqrt]

theorem coefficientEnergyNorm_smul {d : ℕ} (Q : Homogenization.TriadicCube d)
    (A : Homogenization.Book.Ch02.TriadicCoeffFamily d) (c : ℝ)
    (F : Homogenization.Vec d → Homogenization.Vec d) :
    SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q A (fun x => c • F x) =
      |c| * SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q A F := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm
  simp_rw [Homogenization.matVecMul_smul, Homogenization.vecDot_smul_left,
    Homogenization.vecDot_smul_right]
  rw [integral_const_mul, integral_const_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem centeredCube_eq_translate_originCube {d : ℕ} (z : SpatialCoordinates d)
    (m : ℕ) (hr : (0 : ℝ) < 3 ^ m) :
    (centeredCube z ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z
        (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) := by
  ext x
  rw [Homogenization.mem_translateSet_iff_sub_mem]
  rw [centeredCube_eq_pi]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
    Homogenization.openCubeSet, Homogenization.originCube,
    Homogenization.cubeScaleFactor, Pi.zero_apply,
    zpow_natCast]
  simp only [Set.mem_ofPred_eq]
  norm_num
  constructor
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    constructor <;> linarith
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    constructor <;> linarith


end SubdiffusiveProcess.AffineSobolevNorms




