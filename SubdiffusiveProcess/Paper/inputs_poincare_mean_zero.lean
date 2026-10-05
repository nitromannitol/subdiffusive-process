module

public import SubdiffusiveProcess.Paper.inputs_poincare_gradient
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.Sobolev.NativeH1
public import Homogenization.Book.Ch01.Theorems.MultiscalePoincare
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicCovariance
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.ContinuousDiscreteKBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq
public import SubdiffusiveProcess.Section2.CoarseGrainedPoincare

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_inputs_poincare_mean_zero_unit_native {d : ℕ} [NeZero d]
    (v : Homogenization.H1Function
      (Homogenization.openCubeSet (Homogenization.originCube d 0)))
    (havg : Homogenization.cubeAverage (Homogenization.originCube d 0)
      (fun x => v x) = 0) :
    Homogenization.cubeLpNorm (Homogenization.originCube d 0) (2 : ℝ≥0∞)
        (fun x => v x) ≤
      (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant
          (Homogenization.originCube d 0) * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ∑ i : Fin d, Homogenization.cubeBesovCircNorm
          (Homogenization.originCube d 0) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => v.grad x i) := by
  let Q := Homogenization.originCube d 0
  have hnative :=
    Homogenization.CubeLocalFullCircPoincareVectorEstimate.fluctuation_partialNormTop_two_le_sum_circNorm
      (Homogenization.Book.Ch01.Legacy.h1_descendantLocalFullCircPoincare Q v 0)
      (fun i => v.grad_coord_memL2_normalizedCubeMeasure i)
      (s := 0) (by norm_num) (by norm_num)
      (by
        exact mul_nonneg
          (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant_nonneg Q)
          (Real.rpow_nonneg (by norm_num) _))
  have hfluct : Homogenization.cubeFluctuation Q (fun x => v x) = fun x => v x := by
    funext x
    simp [Homogenization.cubeFluctuation, Q, havg]
  have hfluct_avg : Homogenization.cubeAverage Q
      (Homogenization.cubeFluctuation Q (fun x => v x)) = 0 := by
    rw [Homogenization.cubeAverage_cubeFluctuation]
  have hdouble : Homogenization.cubeFluctuation Q
      (Homogenization.cubeFluctuation Q (fun x => v x)) =
      Homogenization.cubeFluctuation Q (fun x => v x) := by
    funext x
    simp [Homogenization.cubeFluctuation, hfluct_avg]
  have htop :
      Homogenization.cubeBesovPartialNormTop Q 0 (2 : ℝ≥0∞) 0
        (Homogenization.cubeFluctuation Q (fun x => v x)) =
      Homogenization.cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v x) := by
    calc
      Homogenization.cubeBesovPartialNormTop Q 0 (2 : ℝ≥0∞) 0
          (Homogenization.cubeFluctuation Q (fun x => v x)) =
          Homogenization.cubeBesovDepthSeminorm Q 0 (2 : ℝ≥0∞)
            (Homogenization.cubeFluctuation Q (fun x => v x)) 0 := by
              simp [Homogenization.cubeBesovPartialNormTop,
                Homogenization.cubeBesovPartialSeminormTop]
      _ = Homogenization.cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v x) := by
        unfold Homogenization.cubeBesovDepthSeminorm
        rw [Homogenization.cubeBesovDepthWeight_depth_zero]
        have hweight : Homogenization.cubeBesovScaleWeight 0 Q = 1 := by
          simp [Homogenization.cubeBesovScaleWeight]
        rw [hweight]
        rw [Homogenization.cubeBesovDepthAverage_depth_zero]
        rw [Homogenization.cubeBesovOscillation]
        rw [hdouble]
        rw [hfluct]
        simp only [Homogenization.cubeLpNorm]
        norm_num
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
        exact abs_of_nonneg ENNReal.toReal_nonneg
  rw [← htop]
  simpa [Q] using hnative

theorem aux_inputs_poincare_mean_zero_unit_coarse {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (A : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hSymm : ∀ Q, Homogenization.Book.Ch02.CoeffOn.IsSymmetric (A.coeffOn Q))
    (v : Homogenization.H1Function
      (Homogenization.openCubeSet (Homogenization.originCube d 0)))
    (havg : Homogenization.cubeAverage (Homogenization.originCube d 0)
      (fun x => v x) = 0) :
    Homogenization.cubeLpNorm (Homogenization.originCube d 0) (2 : ℝ≥0∞)
        (fun x => v x) ≤
      (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant
          (Homogenization.originCube d 0) * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        (Fintype.card (Fin d) : ℝ) *
        (SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor 1
            (.finite 1) *
          Real.rpow
            (SubdiffusiveProcess.CoarseGrainingVocab.lambda (Homogenization.originCube d 0) 1
              (.finite 1) A) (-1 / 2) *
          SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm
            (Homogenization.originCube d 0) A v.grad) := by
  let Q := Homogenization.originCube d 0
  have hzeroMem : Homogenization.MemVectorL2
      (Homogenization.openCubeSet Q) (fun _ => (0 : Fin d → ℝ)) := by
    change MeasureTheory.MemLp (fun _ : Homogenization.Vec d => (0 : Fin d → ℝ))
      2 (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q))
    simp
  have hzeroSol : Homogenization.IsSolenoidalOn
      (Homogenization.openCubeSet Q) (fun _ => (0 : Fin d → ℝ)) := by
    intro φ
    simp [Homogenization.vecDot]
  have hcoarse := _root_.SubdiffusiveProcess.Section2.coarse_grained_poincare hd A hSymm
    1 (by norm_num) (by norm_num)
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) (by norm_num) 0 v
      (fun _ => (0 : Fin d → ℝ)) hzeroMem hzeroSol
  have hbesov := hcoarse.1
  have hpartial : ∀ N : ℕ,
      Homogenization.cubeBesovNegativeVectorPartialSeminorm Q 1 N v.grad ≤
        SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          Q 1 (.finite 1) v.grad := by
    intro N
    calc
      Homogenization.cubeBesovNegativeVectorPartialSeminorm Q 1 N v.grad ≤
        Homogenization.cubeBesovNegativeVectorSeminorm Q 1 v.grad :=
        Homogenization.cubeBesovNegativeVectorPartialSeminorm_le_seminorm_of_memLp
          Q (by norm_num) v.grad N (by
            change MeasureTheory.MemLp (fun x : Homogenization.Vec d => v.grad x)
              2 (Homogenization.normalizedCubeMeasure Q)
            rw [MeasureTheory.memLp_pi_iff]
            intro i
            exact v.grad_coord_memL2_normalizedCubeMeasure i)
      _ = Homogenization.Book.Ch03.scaleNormalizedNegativeBesovVectorNorm
            Q 1 (.finite 1) v.grad := by
        symm
        exact Homogenization.Book.Ch03.scaleNormalizedNegativeBesovVectorNorm_finite_one_eq_cubeBesovNegativeVectorSeminorm
          Q 1 v.grad
      _ = SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            Q 1 (.finite 1) v.grad := by
        simp [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm,
          Real.rpow_one]
  have hcomp : ∀ i : Fin d,
      Homogenization.cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => v.grad x i) ≤
        SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          Q 1 (.finite 1) v.grad := by
    intro i
    calc
      Homogenization.cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => v.grad x i) ≤
          Homogenization.cubeBesovScaleWeight (-1) Q *
            SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
              Q 1 (.finite 1) v.grad :=
        Homogenization.cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
          Q 1 v.grad i hpartial
      _ = SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            Q 1 (.finite 1) v.grad := by
        simp [Homogenization.cubeBesovScaleWeight, Q]
  have hsum :
      (∑ i : Fin d, Homogenization.cubeBesovCircNorm Q 1 (2 : ℝ≥0∞)
        (1 : ℝ≥0∞) (fun x => v.grad x i)) ≤
        (Fintype.card (Fin d) : ℝ) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            Q 1 (.finite 1) v.grad := by
    calc
      _ ≤ ∑ _i : Fin d,
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            Q 1 (.finite 1) v.grad :=
        Finset.sum_le_sum fun i _ => hcomp i
      _ = _ := by simp
  have hnative := aux_inputs_poincare_mean_zero_unit_native v havg
  have hK : 0 ≤ Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant Q *
      (3 : ℝ) ^ ((d : ℝ) + 1) := by
    exact mul_nonneg
      (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant_nonneg Q)
      (Real.rpow_nonneg (by norm_num) _)
  have hcard : 0 ≤ (Fintype.card (Fin d) : ℝ) := by positivity
  calc
    Homogenization.cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v x) ≤
        (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant Q *
          (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ∑ i : Fin d, Homogenization.cubeBesovCircNorm Q 1
            (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => v.grad x i) := hnative
    _ ≤ (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant Q *
          (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) *
            SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
              Q 1 (.finite 1) v.grad) := mul_le_mul_of_nonneg_left hsum hK
    _ = (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant Q *
          (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (Fintype.card (Fin d) : ℝ) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            Q 1 (.finite 1) v.grad := by ring
    _ ≤ (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant Q *
          (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (Fintype.card (Fin d) : ℝ) *
          (SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor 1 (.finite 1) *
            Real.rpow (SubdiffusiveProcess.CoarseGrainingVocab.lambda Q 1 (.finite 1) A)
              (-1 / 2) *
            SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q A v.grad) := by
        apply mul_le_mul_of_nonneg_left hbesov
        exact mul_nonneg hK hcard

theorem aux_inputs_poincare_mean_zero_nativeH1_axis {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : meanZeroSobolevGraph (centeredCube z r hr)) :
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
  have huweak : (u : SobolevData (centeredCube z r hr)) ∈
      weakSobolevGraph (centeredCube z r hr) := by
    exact (SubdiffusiveProcess.mem_meanZeroSobolevGraph_iff
      (u : SobolevData (centeredCube z r hr))).mp u.property |>.1
  let uW : weakSobolevGraph (centeredCube z r hr) := ⟨u, huweak⟩
  obtain ⟨uH, hfun, hgrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph uW
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

theorem aux_inputs_poincare_mean_zero_pullback {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : meanZeroSobolevGraph (centeredCube z r hr)) :
    ∃ v : Homogenization.H1Function
        (Homogenization.openCubeSet (Homogenization.originCube d 0)),
      Homogenization.cubeAverage (Homogenization.originCube d 0)
        (fun x => v x) = 0 ∧
      (∀ x, v.toFun x = r⁻¹ *
        (u : SobolevData (centeredCube z r hr)).1
          (fun j => z j + r * x j)) ∧
      ∀ x i, v.grad x i =
        (u : SobolevData (centeredCube z r hr)).2 i
          (fun j => z j + r * x j) := by
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
  obtain ⟨uA, hfunA, hgradA⟩ :=
    aux_inputs_poincare_mean_zero_nativeH1_axis z r hr u
  let v := Homogenization.CubeCalderonZygmund.axisCubeHarmonicPullback w hr uA
  have hmean : ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      (u : SobolevData (centeredCube z r hr)).1 x = 0 :=
    (SubdiffusiveProcess.mem_meanZeroSobolevGraph_iff
      (u : SobolevData (centeredCube z r hr))).mp u.property |>.2
  have hzeroAxis : ∫ x, uA.toFun x ∂
      volume.restrict (Homogenization.axisCube w r) = 0 := by
    calc
      ∫ x, uA.toFun x ∂volume.restrict (Homogenization.axisCube w r) =
          ∫ x, (u : SobolevData (centeredCube z r hr)).1 x ∂
            volume.restrict (Homogenization.axisCube w r) :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun x => congrFun hfunA x)
      _ = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (u : SobolevData (centeredCube z r hr)).1 x := by
        simp [hset]
      _ = 0 := hmean
  have hzeroNorm : ∫ x, uA.toFun x ∂
      Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure w r = 0 := by
    rw [Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
      w r hr, MeasureTheory.integral_smul_measure, smul_eq_mul, hzeroAxis]
    simp
  have hcomp :=
    (Homogenization.CubeCalderonZygmund.measurePreserving_axisCubeAffine w r).integral_comp
      (Homogenization.CubeCalderonZygmund.axisCubeAffineMeasurableEquiv w hr.ne').measurableEmbedding
      (fun y => uA.toFun y)
  have havg : Homogenization.cubeAverage (Homogenization.originCube d 0)
      (fun x => v x) = 0 := by
    rw [Homogenization.cubeAverage_eq_integral_normalizedCubeMeasure,
      Homogenization.normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
    change (∫ x, v.toFun x ∂volume.restrict
      (Homogenization.openCubeSet (Homogenization.originCube d 0))) = 0
    have hval : ∀ x, v.toFun x = r⁻¹ * uA.toFun
        (Homogenization.CubeCalderonZygmund.axisCubeAffine w r x) := by
      intro x
      exact Homogenization.CubeCalderonZygmund.axisCubeHarmonicPullback_toFun
        w hr uA x
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hval)]
    calc
      ∫ x, r⁻¹ * uA.toFun
          (Homogenization.CubeCalderonZygmund.axisCubeAffine w r x) ∂
            volume.restrict (Homogenization.openCubeSet
              (Homogenization.originCube d 0)) =
          r⁻¹ * ∫ x, uA.toFun
            (Homogenization.CubeCalderonZygmund.axisCubeAffine w r x) ∂
              volume.restrict (Homogenization.openCubeSet
                (Homogenization.originCube d 0)) := by
        rw [MeasureTheory.integral_const_mul]
      _ = r⁻¹ * ∫ y, uA.toFun y ∂
            Homogenization.CubeCalderonZygmund.axisCubeNormalizedMeasure w r := by
        congr 1
      _ = 0 := by rw [hzeroNorm]; simp
  exact ⟨v, havg, by
    intro x
    calc
      v.toFun x = r⁻¹ * uA.toFun
          (Homogenization.CubeCalderonZygmund.axisCubeAffine w r x) :=
        Homogenization.CubeCalderonZygmund.axisCubeHarmonicPullback_toFun
          w hr uA x
      _ = r⁻¹ * (u : SobolevData (centeredCube z r hr)).1
          (fun j => z j + r * x j) := by
        rw [hfunA]
        apply congrArg (fun y => r⁻¹ *
          (u : SobolevData (centeredCube z r hr)).1 y)
        funext j
        simp [Homogenization.CubeCalderonZygmund.axisCubeAffine,
          Homogenization.CubeCalderonZygmund.axisCubeCenter, w]
        ring, by
    intro x i
    rw [Homogenization.CubeCalderonZygmund.axisCubeHarmonicPullback_grad]
    rw [hgradA]
    congr 1
    funext j
    simp [Homogenization.CubeCalderonZygmund.axisCubeAffine,
      Homogenization.CubeCalderonZygmund.axisCubeCenter, w]
    ring⟩

theorem aux_inputs_poincare_mean_zero_l2_transport {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : meanZeroSobolevGraph (centeredCube z r hr))
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

theorem inputs_poincare_mean_zero (d : ℕ) (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) :
    (∃ C : ℝ, 0 < C ∧ (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (u : meanZeroSobolevGraph (centeredCube z r hr)),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        C * r * (Jc.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _)))) := by
  let : NeZero d := ⟨by omega⟩
  let Q := Homogenization.originCube d 0
  let P := SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor 1 (.finite 1)
  have hdiscount : 0 < Homogenization.Book.Ch02.geometricDiscount 1 1 := by
    norm_num [Homogenization.Book.Ch02.geometricDiscount]
  have hP : 0 < P := by
    change 0 < SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor 1 (.finite 1)
    rw [SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor]
    exact Real.rpow_pos_of_pos hdiscount _
  let C0 : ℝ := (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant Q *
    (3 : ℝ) ^ ((d : ℝ) + 1)) * (Fintype.card (Fin d) : ℝ) * P
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (Homogenization.Book.Ch01.Legacy.fullVectorPoincareConstant_nonneg Q)
      (Real.rpow_nonneg (by norm_num) _)) (by positivity)) hP.le
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro z r hr a u
  obtain ⟨v, havg, hfun, hgrad⟩ := aux_inputs_poincare_mean_zero_pullback z r hr u
  obtain ⟨uA, hfunA, _hgradA⟩ := aux_inputs_poincare_mean_zero_nativeH1_axis z r hr u
  have hL2 := aux_inputs_poincare_mean_zero_l2_transport z r hr u uA hfunA v hfun
  let uw : weakSobolevGraph (centeredCube z r hr) :=
    ⟨u.val, ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩
  let A := aux_inputs_poincare_gradient_symmFamily (Jc.chart z r hr a z r)
  have henergy := aux_inputs_poincare_gradient_energy Jc z r hr a uw v hgrad
  have hlam : Jc.lam z r hr a z r 1 1 =
      SubdiffusiveProcess.CoarseGrainingVocab.lambda Q 1 (.finite 1) A := by
    simpa [Q, A] using aux_inputs_poincare_gradient_lambda_symm Jc z r hr a
      1 (by norm_num) 1 (by norm_num)
  have hnative := aux_inputs_poincare_mean_zero_unit_coarse hd A
    (fun R => aux_inputs_poincare_gradient_symmFamily_symmetric (Jc.chart z r hr a z r) R)
    v havg
  rw [← hlam, henergy] at hnative
  have hbound : ‖(u : SobolevData (centeredCube z r hr)).1‖ /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
      C0 * r * (Jc.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
        normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
          (sobolevGradient (u : SobolevData _)) := by
    rw [hL2]
    convert mul_le_mul_of_nonneg_left hnative hr.le using 1 ; dsimp [C0, Q, P, uw] ; ring
  apply hbound.trans
  have hlast : 0 ≤ r * (Jc.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
      normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (u : SobolevData _)) := by
    unfold normalizedEnergyNorm
    exact mul_nonneg (mul_nonneg hr.le
      (Real.rpow_nonneg (Jc.lam_pos z r hr a z r 1 1).le _)) (Real.sqrt_nonneg _)
  nlinarith

end SubdiffusiveProcess.Paper
