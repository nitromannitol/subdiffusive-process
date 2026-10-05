module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PaperDualReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PositiveFractionalDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DifferenceFields
public import SubdiffusiveProcess.Frozen.Section6.Defs.OrdinaryVectorHMinusOne
public import Homogenization.Sobolev.Foundations.PoincareZeroTrace
public import Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12NormalizedPartition

@[expose] public section

/-!
# From the manuscript negative fractional norm to ordinary `H⁻¹`

Scalar compactly supported unit-gradient tests are inserted one coordinate at
a time into the manuscript vector test carrier.  The positive fractional
estimate for unit-cube `H¹` fields then gives a finite dimension/order
constant, and the frozen ordinary vector norm is read coordinatewise.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

private abbrev UnitSmoothTest (d : ℕ) [NeZero d] :=
  NegativeSobolev.SmoothTestFunction
    (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))

private noncomputable def unitSmoothTestH10 {d : ℕ} [NeZero d]
    (phi : UnitSmoothTest d) :
    H10Function (openCubeSet (originCube d 0)) :=
  H10Function.ofContDiff (isOpen_openCubeSet (originCube d 0)) phi.contDiff
    phi.hasCompactSupport phi.tsupport_subset

private theorem unitSmoothTest_seminorm_two_eq_gradNorm {d : ℕ} [NeZero d]
    (phi : UnitSmoothTest d) :
    NegativeSobolev.smoothTestSeminorm
        (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))
        (Book.Ch02.openCubeSet_nonempty (originCube d 0))
        (2 : ℝ≥0∞) (by norm_num) (by norm_num) phi =
      ‖(unitSmoothTestH10 phi).toH1Function.gradToHilbertVectorL2‖ := by
  unfold NegativeSobolev.smoothTestSeminorm
    BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
    BoundedMeasurableDomain.normalizedEuclideanLpNorm
    BoundedMeasurableDomain.normalizedLpNorm
    BoundedMeasurableDomain.normalizedLpFiniteENorm
  change ENNReal.toReal (eLpNorm
      (fun x ↦ euclideanNorm (phi.gradient x)) 2
      ((isOpenBoundedConvexDomain_openCubeSet (originCube d 0)).toBoundedMeasurableDomain
        (Book.Ch02.openCubeSet_nonempty (originCube d 0))).normalizedVolume) = _
  rw [openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
  have hgrad : (fun x ↦ HilbertVec.ofVec (phi.gradient x)) =
      hilbertifyVecField (unitSmoothTestH10 phi).toH1Function.grad := by
    funext x
    change HilbertVec.ofVec (phi.gradient x) =
      HilbertVec.ofVec ((unitSmoothTestH10 phi).toH1Function.grad x)
    congr 1
  have hmeas : AEStronglyMeasurable (fun x ↦ HilbertVec.ofVec (phi.gradient x))
      (volumeMeasureOn (openCubeSet (originCube d 0))) := by
    rw [hgrad]
    apply aestronglyMeasurable_of_eLpNorm_ne_top (p := 2)
    rw [CubeCalderonZygmund.eLpNorm_hilbertify_grad_two_eq_ofReal_norm_gradToHilbertVectorL2]
    exact ENNReal.ofReal_ne_top
  simp only [euclideanNorm_eq_norm_ofVec, eLpNorm_norm _ hmeas]
  rw [hgrad]
  rw [CubeCalderonZygmund.eLpNorm_hilbertify_grad_two_eq_ofReal_norm_gradToHilbertVectorL2]
  rw [ENNReal.toReal_ofReal (norm_nonneg _)]

private noncomputable def singleCoordinateSmoothTestField {d : ℕ} [NeZero d]
    (s : FractionalOrder) (i : Fin d) (phi : UnitSmoothTest d) :
    CubeEuclideanWspSmoothTest (originCube d 0) s FiniteLpExponent.two where
  toField := fun x ↦ Pi.single i (phi x)
  contDiff := by
    rw [contDiff_pi]
    intro j
    by_cases hji : j = i
    · convert phi.contDiff using 1
      funext x
      simp [hji]
    · convert (contDiff_const :
          ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d ↦ (0 : ℝ))) using 1
      funext x
      simp [hji]

private noncomputable def singleCoordinateCubeVectorH1 {d : ℕ} [NeZero d]
    (i : Fin d) (phi : UnitSmoothTest d) :
    CubeVectorH1Function (originCube d 0) where
  coord j := if i = j then (unitSmoothTestH10 phi).toH1Function else 0

private theorem h1Function_zero_gradientCoordL2NormSum
    {d : ℕ} {U : Set (Vec d)} :
    (0 : H1Function U).gradientCoordL2NormSum = 0 := by
  apply le_antisymm
  · calc
      (0 : H1Function U).gradientCoordL2NormSum ≤
          d * ‖(0 : H1Function U).gradToVectorL2‖ :=
        H1Function.gradientCoordL2NormSum_le 0
      _ = 0 := by
        have hz : (0 : H1Function U).gradToVectorL2 = 0 := by
          apply MeasureTheory.Lp.ext
          filter_upwards
              [H1Function.coeFn_gradToVectorL2 (0 : H1Function U),
                MeasureTheory.Lp.coeFn_zero (E := Vec d) (p := (2 : ENNReal))
                  (μ := volumeMeasureOn U)]
            with x hx hzero
          rw [hx, hzero]
          rfl
        rw [hz, norm_zero, mul_zero]
  · exact H1Function.gradientCoordL2NormSum_nonneg 0

private theorem singleCoordinateCubeVectorH1_toField {d : ℕ} [NeZero d]
    (i : Fin d) (phi : UnitSmoothTest d) :
    (singleCoordinateCubeVectorH1 i phi).toField =
      (singleCoordinateSmoothTestField
        (s := ⟨(2 : ℝ)⁻¹, by constructor <;> norm_num⟩) i phi).toField := by
  funext x j
  by_cases hji : i = j <;>
    simp [singleCoordinateCubeVectorH1, singleCoordinateSmoothTestField,
      CubeVectorH1Function.toField, unitSmoothTestH10, hji,
      H10Function.ofContDiff, H1Function.ofContDiff]

private theorem singleCoordinateCubeVectorH1_gradientCoordL2NormSum
    {d : ℕ} [NeZero d] (i : Fin d) (phi : UnitSmoothTest d) :
    (singleCoordinateCubeVectorH1 i phi).gradientCoordL2NormSum =
      (unitSmoothTestH10 phi).toH1Function.gradientCoordL2NormSum := by
  unfold CubeVectorH1Function.gradientCoordL2NormSum
    singleCoordinateCubeVectorH1
  change (∑ j : Fin d,
      (if i = j then (unitSmoothTestH10 phi).toH1Function else 0).gradientCoordL2NormSum) = _
  calc
    (∑ j : Fin d,
        (if i = j then (unitSmoothTestH10 phi).toH1Function else 0).gradientCoordL2NormSum) =
        (if i = i then (unitSmoothTestH10 phi).toH1Function else 0).gradientCoordL2NormSum := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j _hj hji
        simp only [Ne.symm hji, ite_false]
        exact h1Function_zero_gradientCoordL2NormSum
      · simp
    _ = _ := by simp

/-- A finite zero-trace Poincare constant on the fixed centered unit cube. -/
noncomputable def unitCenteredH10PoincareConstant (d : ℕ) [NeZero d] : ℝ :=
  (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))).choose

private theorem unitCenteredH10PoincareConstant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ unitCenteredH10PoincareConstant d :=
  (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))).choose_spec.1

private theorem unitCenteredH10PoincareConstant_bound {d : ℕ} [NeZero d]
    (w : H10Function (openCubeSet (originCube d 0))) :
    ‖w.toH1Function.toScalarL2‖ ≤
      unitCenteredH10PoincareConstant d *
        w.toH1Function.gradientCoordL2NormSum :=
  (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))).choose_spec.2 w

private theorem singleCoordinateCubeVectorH1_normalizedL2
    {d : ℕ} [NeZero d] (i : Fin d) (phi : UnitSmoothTest d) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (unitEuclideanL2FieldOfCubeVectorH1
          (singleCoordinateCubeVectorH1 i phi)) =
      ENNReal.ofReal ‖(unitSmoothTestH10 phi).toH1Function.toScalarL2‖ := by
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpENorm
  rw [← normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume,
    normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
  have hfield :
      (unitEuclideanL2FieldOfCubeVectorH1
        (singleCoordinateCubeVectorH1 i phi)).toField =
        fun x ↦ Pi.single i (phi x) := by
    funext x j
    by_cases hij : i = j <;> simp [unitEuclideanL2FieldOfCubeVectorH1,
      singleCoordinateCubeVectorH1, CubeVectorH1Function.toField,
      unitSmoothTestH10, H10Function.ofContDiff, H1Function.ofContDiff,
      hij]
  rw [hfield]
  simp only [euclideanNorm_eq_norm_ofVec]
  change eLpNorm (fun x ↦ ‖HilbertVec.ofVec
      (Pi.single i (phi x))‖) 2
      (volumeMeasureOn (openCubeSet (originCube d 0))) = _
  have hpoint : (fun x ↦ ‖HilbertVec.ofVec (Pi.single i (phi x))‖) =
      fun x ↦ ‖(phi x : ℝ)‖ := by
    funext x
    exact PiLp.norm_single 2 (fun _ : Fin d ↦ ℝ) i (phi x)
  rw [hpoint, eLpNorm_norm _ (by
    simpa only [volumeMeasureOn] using! phi.contDiff.continuous.aestronglyMeasurable.restrict)]
  let w := (unitSmoothTestH10 phi).toH1Function
  have hfun : w.toFun = (phi : Vec d → ℝ) := rfl
  rw [← hfun]
  exact (MeasureTheory.Lp.enorm_toLp w.memL2).symm.trans
    (ofReal_norm w.toScalarL2).symm

/-- Uniform real `H¹` budget for a one-coordinate test from the normalized
gradient unit ball. -/
noncomputable def singleCoordinateH1BudgetConstant
    (d : ℕ) [NeZero d] : ℝ :=
  unitCenteredH10PoincareConstant d * d + d

private theorem singleCoordinateH1BudgetConstant_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤ singleCoordinateH1BudgetConstant d := by
  unfold singleCoordinateH1BudgetConstant
  exact add_nonneg
    (mul_nonneg (unitCenteredH10PoincareConstant_nonneg d) (Nat.cast_nonneg d))
    (Nat.cast_nonneg d)

private theorem unitCubeVectorH1ENormBudget_singleCoordinate_le
    {d : ℕ} [NeZero d] (i : Fin d) (phi : UnitSmoothTest d)
    (hphi : NegativeSobolev.smoothTestSeminorm
        (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))
        (Book.Ch02.openCubeSet_nonempty (originCube d 0))
        (2 : ℝ≥0∞) (by norm_num) (by norm_num) phi ≤ 1) :
    unitCubeVectorH1ENormBudget (singleCoordinateCubeVectorH1 i phi) ≤
      ENNReal.ofReal (singleCoordinateH1BudgetConstant d) := by
  let w := (unitSmoothTestH10 phi).toH1Function
  have hhilbert : ‖w.gradToHilbertVectorL2‖ ≤ 1 := by
    rw [← unitSmoothTest_seminorm_two_eq_gradNorm phi]
    exact hphi
  have hgrad : w.gradientCoordL2NormSum ≤ (d : ℝ) := by
    calc
      w.gradientCoordL2NormSum ≤ d * ‖w.gradToVectorL2‖ :=
        w.gradientCoordL2NormSum_le
      _ ≤ d * ‖w.gradToHilbertVectorL2‖ := by
        gcongr
        exact w.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
      _ ≤ d * 1 := by gcongr
      _ = d := mul_one _
  have hvalue : ‖w.toScalarL2‖ ≤
      unitCenteredH10PoincareConstant d * d := by
    calc
      ‖w.toScalarL2‖ ≤
          unitCenteredH10PoincareConstant d * w.gradientCoordL2NormSum :=
        unitCenteredH10PoincareConstant_bound (unitSmoothTestH10 phi)
      _ ≤ unitCenteredH10PoincareConstant d * d :=
        mul_le_mul_of_nonneg_left hgrad
          (unitCenteredH10PoincareConstant_nonneg d)
  have hCd : 0 ≤ unitCenteredH10PoincareConstant d * (d : ℝ) :=
    mul_nonneg (unitCenteredH10PoincareConstant_nonneg d) (Nat.cast_nonneg d)
  unfold unitCubeVectorH1ENormBudget
  rw [singleCoordinateCubeVectorH1_normalizedL2 i phi,
    singleCoordinateCubeVectorH1_gradientCoordL2NormSum]
  change ENNReal.ofReal ‖w.toScalarL2‖ +
      ENNReal.ofReal w.gradientCoordL2NormSum ≤ _
  calc
    ENNReal.ofReal ‖w.toScalarL2‖ +
        ENNReal.ofReal w.gradientCoordL2NormSum ≤
      ENNReal.ofReal (unitCenteredH10PoincareConstant d * d) +
        ENNReal.ofReal (d : ℝ) :=
      add_le_add (ENNReal.ofReal_le_ofReal hvalue)
        (ENNReal.ofReal_le_ofReal hgrad)
    _ = ENNReal.ofReal (singleCoordinateH1BudgetConstant d) := by
      rw [← ENNReal.ofReal_add hCd (Nat.cast_nonneg d)]
      unfold singleCoordinateH1BudgetConstant
      rfl

/-- Finite dimension/order constant for inserting one scalar `H¹₀` unit
test into the paper's vector `Hˢ` carrier. -/
noncomputable def negativeNormReadoutConstant
    (s : FractionalOrder) (d : ℕ) [NeZero d] : ℝ≥0∞ :=
  (scaledVectorDatumFractionalConstant s d + 1) *
    ENNReal.ofReal (singleCoordinateH1BudgetConstant d)

theorem negativeNormReadoutConstant_lt_top
    (s : FractionalOrder) (d : ℕ) [NeZero d] :
    negativeNormReadoutConstant s d < ∞ := by
  unfold negativeNormReadoutConstant
  exact ENNReal.mul_lt_top
    (ENNReal.add_lt_top.mpr
      ⟨scaledVectorDatumFractionalConstant_lt_top s d, ENNReal.one_lt_top⟩)
    ENNReal.ofReal_lt_top

private theorem paperFractionalFullNorm_singleCoordinate_le
    {d : ℕ} [NeZero d] (s : FractionalOrder) (i : Fin d)
    (phi : UnitSmoothTest d)
    (hphi : NegativeSobolev.smoothTestSeminorm
        (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))
        (Book.Ch02.openCubeSet_nonempty (originCube d 0))
        (2 : ℝ≥0∞) (by norm_num) (by norm_num) phi ≤ 1) :
    paperFractionalFullNorm (originCube d 0) s FiniteLpExponent.two
        (singleCoordinateSmoothTestField s i phi).toField ≤
      negativeNormReadoutConstant s d := by
  let V := singleCoordinateCubeVectorH1 i phi
  let T := singleCoordinateSmoothTestField s i phi
  have hVT : V.toField = T.toField := by
    funext x j
    by_cases hij : i = j <;>
      simp [V, T, singleCoordinateCubeVectorH1, singleCoordinateSmoothTestField,
        CubeVectorH1Function.toField, unitSmoothTestH10,
        H10Function.ofContDiff, H1Function.ofContDiff, hij]
  have hfield :
      (centeredCubeScaledVectorDilation (1 : ℝ) 0 V).toField = T.toField := by
    funext x
    rw [centeredCubeScaledVectorDilation_toField]
    simp only [centeredCubeScale_zero, inv_one, mul_one, one_smul]
    exact congrFun hVT x
  have hsemi :
      paperFractionalSeminorm (originCube d 0) s FiniteLpExponent.two T.toField ≤
        scaledVectorDatumFractionalConstant s d * unitCubeVectorH1ENormBudget V := by
    rw [← hfield]
    simpa [scaledVectorDatumFractionalENormBound] using!
      paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_h1Budget
        (1 : ℝ) 0 s V
  have hL2 :
      (cubeBoundedMeasurableDomain (originCube d 0)).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) T.toField ≤ unitCubeVectorH1ENormBudget V := by
    have heq := singleCoordinateCubeVectorH1_normalizedL2 i phi
    unfold unitCubeVectorH1ENormBudget
    rw [← hVT]
    simp only [cubeBoundedMeasurableDomain, unitCenteredCubeDomain] at heq ⊢
    exact le_add_right le_rfl
  have hbudget := unitCubeVectorH1ENormBudget_singleCoordinate_le i phi hphi
  rw [paperFractionalFullNorm]
  simp only [cubeScaleFactor_originCube, zpow_zero, ENNReal.ofReal_one,
    ENNReal.one_rpow, one_mul]
  calc
    paperFractionalSeminorm (originCube d 0) s FiniteLpExponent.two T.toField +
        (cubeBoundedMeasurableDomain (originCube d 0)).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) T.toField ≤
      scaledVectorDatumFractionalConstant s d * unitCubeVectorH1ENormBudget V +
        unitCubeVectorH1ENormBudget V := add_le_add hsemi hL2
    _ = (scaledVectorDatumFractionalConstant s d + 1) *
        unitCubeVectorH1ENormBudget V := by ring
    _ ≤ (scaledVectorDatumFractionalConstant s d + 1) *
        ENNReal.ofReal (singleCoordinateH1BudgetConstant d) := by
      exact mul_le_mul_right hbudget _
    _ = negativeNormReadoutConstant s d := by unfold negativeNormReadoutConstant; rfl

private theorem smoothPairing_coordinate_eq_vectorPairing
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    (F : L2VectorField (originCube d 0)) (i : Fin d)
    (phi : UnitSmoothTest d) :
    NegativeSobolev.smoothPairing
        (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))
        (Book.Ch02.openCubeSet_nonempty (originCube d 0))
        (2 : ℝ≥0∞) (by norm_num) (fun x ↦ F.toFun x i) (F.memLpCoord i) phi =
      cubeEuclideanNormalizedSmoothPairing
        (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F)
        (singleCoordinateSmoothTestField s i phi) := by
  unfold NegativeSobolev.smoothPairing NegativeSobolev.normalizedPairing
    BoundedMeasurableDomain.pairing BoundedMeasurableDomain.average
    cubeEuclideanNormalizedSmoothPairing
  rw [openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards with x
  simp [l2VectorFieldToCubeEuclideanL2Field,
    singleCoordinateSmoothTestField, vecDot, Pi.single_apply,
    Finset.sum_ite_eq']

private theorem coordinateHMinusOne_le_paperNegativeFractionalDual
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    (F : L2VectorField (originCube d 0)) (i : Fin d) :
    Ch01.normalizedZeroBoundaryHMinusOneSeminorm
        (openCubeSet (originCube d 0))
        (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))
        (Book.Ch02.openCubeSet_nonempty (originCube d 0))
        (fun x ↦ F.toFun x i) (F.memLpCoord i) ≤
      negativeNormReadoutConstant s d *
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet (originCube d 0)
  let hne := Book.Ch02.openCubeSet_nonempty (originCube d 0)
  change NegativeSobolev.smoothNegativeSobolevSeminorm hU hne
      (2 : ℝ≥0∞) (by norm_num) (by norm_num)
      (fun x ↦ F.toFun x i) (F.memLpCoord i) ≤ _
  rw [NegativeSobolev.smoothNegativeSobolevSeminorm_eq_abs
    hU hne (2 : ℝ≥0∞) (by norm_num) (by norm_num)]
  unfold NegativeSobolev.smoothNegativeSobolevAbsSeminorm
  refine iSup_le fun phi ↦ ?_
  let T := singleCoordinateSmoothTestField s i phi.1
  let D := paperNegativeFractionalDual (originCube d 0) s
    FiniteLpExponent.two
      (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F)
  let Tc : CubeEuclideanWspSmoothTest (originCube d 0) s
      FiniteLpExponent.two.conjugate :=
    { toField := T.toField
      contDiff := T.contDiff }
  have hpair :
      ENNReal.ofReal
          |cubeEuclideanNormalizedSmoothPairing
            (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F) T| ≤
        D * paperFractionalFullNorm (originCube d 0) s
          FiniteLpExponent.two T.toField := by
    have hpEq : cubeEuclideanNormalizedSmoothPairing
        (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F) T =
        cubeEuclideanNormalizedSmoothPairing
          (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F) Tc := by
      rfl
    rw [hpEq]
    simpa only [Tc, FiniteLpExponent.conjugate_two, D] using!
      (ofReal_abs_normalizedSmoothPairing_le_paperNegativeFractionalDual_mul_fullNorm
        (p := FiniteLpExponent.two)
        (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F) Tc)
  rw [smoothPairing_coordinate_eq_vectorPairing s F i phi.1]
  calc
    ENNReal.ofReal
        |cubeEuclideanNormalizedSmoothPairing
          (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F) T| ≤
      D * paperFractionalFullNorm (originCube d 0) s
        FiniteLpExponent.two T.toField := hpair
    _ ≤ D * negativeNormReadoutConstant s d := by
      exact mul_le_mul_right
        (paperFractionalFullNorm_singleCoordinate_le s i phi.1 phi.2) D
    _ = negativeNormReadoutConstant s d *
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F) := by
      simp only [D]
      ring

/-- The manuscript `H⁻s` dual controls the frozen componentwise ordinary
`H⁻¹` norm on the centered unit cube. -/
theorem ordinaryVectorHMinusOne_le_paperNegativeFractionalDual
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    (F : L2VectorField (originCube d 0)) :
    ordinaryVectorHMinusOne (originCube d 0) F ≤
      ((d : ℕ) : ℝ≥0∞) * negativeNormReadoutConstant s d *
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F) := by
  unfold ordinaryVectorHMinusOne
  let D := paperNegativeFractionalDual (originCube d 0) s
    FiniteLpExponent.two
      (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) F)
  calc
    (∑ i : Fin d,
      Ch01.normalizedZeroBoundaryHMinusOneSeminorm
        (openCubeSet (originCube d 0))
        (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))
        (Book.Ch02.openCubeSet_nonempty (originCube d 0))
        (fun x ↦ F.toFun x i) (F.memLpCoord i)) ≤
      ∑ _i : Fin d, negativeNormReadoutConstant s d * D := by
        exact Finset.sum_le_sum fun i _ ↦
          coordinateHMinusOne_le_paperNegativeFractionalDual s F i
    _ = ((d : ℕ) : ℝ≥0∞) * negativeNormReadoutConstant s d * D := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      ring
    _ = _ := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
