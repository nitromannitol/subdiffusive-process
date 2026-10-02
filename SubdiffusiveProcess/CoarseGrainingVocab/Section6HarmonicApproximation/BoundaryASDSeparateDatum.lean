import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDNormalization
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDScalar
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryTrace
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.RoughDirichletMinimality
import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.EnergySplit
import Homogenization.Book.Ch03.Theorems.CoarsePoincare
import Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Adding a homogeneous solution to a forced solution preserves the force. -/
theorem isForcedEquation_add_zero
    {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    {u v : H1Function (openCubeSet Q)}
    (hu : IsForcedEquation Q a u g)
    (hv : IsForcedEquation Q a v (fun _ ↦ 0)) :
    IsForcedEquation Q a (u + v) g := by
  intro phi
  have huInt := integrableOn_flux_pairing Q a u phi
  have hvInt := integrableOn_flux_pairing Q a v phi
  have hsplit :
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) ((u + v).grad x))
            (phi.toH1Function.grad x) ∂volume =
        (∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume) +
        ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
            (phi.toH1Function.grad x) ∂volume := by
    rw [← integral_add huInt hvInt]
    apply integral_congr_ae
    filter_upwards with x
    rw [H1Function.add_grad, matVecMul_add, vecDot_add_left]
  have hvzero :
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
            (phi.toH1Function.grad x) ∂volume = 0 := by
    have h := hv phi
    simpa [vecDot] using h
  calc
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) ((u + v).grad x))
          (phi.toH1Function.grad x) ∂volume =
      (∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume) + 0 := by rw [hsplit, hvzero]
    _ = ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
      rw [add_zero, hu phi]

/-- The sum of the canonical forced zero-trace corrector and a zero-force
datum lift is a forced Dirichlet solution with the original datum. -/
noncomputable def splitDirichletForcedCubeSolution
    {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    (rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
    (h : H1Function (openCubeSet Q)) (hw : w.boundaryData = h) :
    DirichletForcedCubeSolution Q a g where
  toH1 :=
    (boundaryForcedCaccioppoliCorrectorOpenH10
      (Q := Q) (a := a) rho).toH1Function + w.toH1
  boundaryData := h
  weakSolution := isForcedEquation_add_zero
    (boundaryForcedCaccioppoliCorrectorForcedCubeSolution
      (Q := Q) (a := a) rho).weakSolution w.weakSolution
  zeroTraceDifference := by
    let r0 := boundaryForcedCaccioppoliCorrectorOpenH10
      (Q := Q) (a := a) rho
    let rw := w.zeroTraceDifferenceH10
    refine ⟨r0 + rw, ?_⟩
    filter_upwards [w.zeroTraceDifferenceH10_toFun_ae_eq] with x hx
    change (r0.toH1Function + rw.toH1Function).toFun x = _
    rw [H1Function.add_toFun]
    change r0.toH1Function.toFun x + rw.toH1Function.toFun x = _
    rw [hx, hw]
    change r0.toH1Function.toFun x + (w.toH1.toFun x - h.toFun x) =
      r0.toH1Function.toFun x + w.toH1.toFun x - h.toFun x
    ring

@[simp] theorem splitDirichletForcedCubeSolution_boundaryData
    {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    (rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
    (h : H1Function (openCubeSet Q)) (hw : w.boundaryData = h) :
    (splitDirichletForcedCubeSolution rho w h hw).boundaryData = h :=
  rfl

@[simp] theorem splitDirichletForcedCubeSolution_toH1
    {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    (rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
    (h : H1Function (openCubeSet Q)) (hw : w.boundaryData = h) :
    (splitDirichletForcedCubeSolution rho w h hw).toH1 =
      (boundaryForcedCaccioppoliCorrectorOpenH10
        (Q := Q) (a := a) rho).toH1Function + w.toH1 :=
  rfl

/-- A zero-force public Dirichlet solution is a Chapter-2 harmonic solution. -/
noncomputable def cubeSolutionOfZeroForceDirichlet
    {Q : TriadicCube d} {a : CoeffFamily d}
    (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0)) :
    CubeSolution Q a where
  toH1 := w.toH1
  isHarmonic := by
    refine ⟨w.toH1.isPotentialOn, ?_⟩
    intro phi
    have hweak := w.weakSolution phi
    simpa [vecDot] using hweak

omit [NeZero d] in
@[simp] theorem cubeSolutionOfZeroForceDirichlet_toH1
    {Q : TriadicCube d} {a : CoeffFamily d}
    (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0)) :
    (cubeSolutionOfZeroForceDirichlet w).toH1 = w.toH1 :=
  rfl

omit [NeZero d] in


theorem cubeBesovNegativeVectorSeminormTwo_le_seminorm_of_memLp
    (Q : TriadicCube d) {r : ℝ} (hr : 0 < r) (F : Vec d → Vec d)
    (hF : MemLp F (2 : ENNReal) (normalizedCubeMeasure Q)) :
    cubeBesovNegativeVectorSeminormTwo Q r F ≤
      cubeBesovNegativeVectorSeminorm Q r F := by
  apply cubeBesovNegativeVectorSeminormTwo_le_of_qone_partialBound
  intro N
  exact cubeBesovNegativeVectorPartialSeminorm_le_seminorm_of_memLp
    Q hr F N hF

omit [NeZero d] in
/-- The two public energy norms agree on the zero-force Dirichlet solution
viewed as a harmonic cube solution. -/
theorem solutionEnergyNorm_cubeSolutionOfZeroForceDirichlet
    {Q : TriadicCube d} {a : CoeffFamily d}
    (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0)) :
    solutionEnergyNorm Q a (cubeSolutionOfZeroForceDirichlet w) =
      dirichletForcedSolutionEnergyNorm Q a w := by
  rw [dirichletForcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField]
  unfold solutionEnergyNorm
  congr 1
  calc
    Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q)
        (cubeSolutionOfZeroForceDirichlet w) =
      localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) w.toH1 := by
        rfl
    _ = cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a) w.toH1.grad) :=
      (cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue
        Q a w.toH1).symm

/-- At the fixed exponent `1/2`, the harmonic datum lift has a finite-`2`
negative Besov bound with only the source lower-ellipticity factor at `t`.
Fixing the exponent is what avoids an additional inverse power of `t` in the
datum row. -/
theorem zeroForceDirichlet_negativeBesovTwo_half_le
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
    (ht : 0 < t) (ht4 : t ≤ 1 / 4) :
    cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) w.toH1.grad ≤
      poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) *
        poincareLowerEllipticityFactor Q a t (.finite 1) *
          dirichletForcedSolutionEnergyNorm Q a w := by
  have hwCube : MemVectorL2 (cubeSet Q) w.toH1.grad := by
    rw [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact w.toH1.grad_memVectorL2
  have hwLp : MemLp w.toH1.grad (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hwCube
  have htwo := cubeBesovNegativeVectorSeminormTwo_le_seminorm_of_memLp
    Q (by norm_num : (0 : ℝ) < 1 / 2) w.toH1.grad hwLp
  have hone := (coarsePoincareTheory Q a).gradient_negativeBesov_le
    (q := .finite 1)
    (cubeSolutionOfZeroForceDirichlet w)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  rw [scaleNormalizedNegativeBesovVectorNorm_finite_one_eq_cubeBesovNegativeVectorSeminorm]
    at hone
  have hmono : Ch02.lambdaSq Q t (.finite 1) a ≤
      Ch02.lambdaSq Q (1 / 2 : ℝ) (.finite 1) a :=
    Ch02.lambdaSq_finite_mono Q a ht (by linarith only [ht4]) (by norm_num)
  have htLam : 0 < Ch02.lambdaSq Q t (.finite 1) a :=
    Ch02.lambdaSq_finite_pos Q a ht (by norm_num)
  have hlower : poincareLowerEllipticityFactor Q a (1 / 2 : ℝ) (.finite 1) ≤
      poincareLowerEllipticityFactor Q a t (.finite 1) := by
    unfold poincareLowerEllipticityFactor
    exact Real.rpow_le_rpow_of_nonpos htLam hmono (by norm_num)
  have hdisc : 0 ≤ poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) := by
    unfold poincareDiscountFactor
    exact Real.rpow_nonneg (geometricDiscount_pos (by norm_num)).le _
  have henergy : 0 ≤ dirichletForcedSolutionEnergyNorm Q a w := by
    unfold dirichletForcedSolutionEnergyNorm h1EnergyNormOnCube
    exact Real.sqrt_nonneg _
  calc
    cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) w.toH1.grad ≤
        cubeBesovNegativeVectorSeminorm Q (1 / 2 : ℝ) w.toH1.grad := htwo
    _ ≤ poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) *
        poincareLowerEllipticityFactor Q a (1 / 2 : ℝ) (.finite 1) *
          solutionEnergyNorm Q a (cubeSolutionOfZeroForceDirichlet w) := by
      simpa [coarsePoincareGradientRHS, solutionGradientField] using hone
    _ ≤ poincareDiscountFactor (1 / 2 : ℝ) (.finite 1) *
        poincareLowerEllipticityFactor Q a t (.finite 1) *
          dirichletForcedSolutionEnergyNorm Q a w := by
      rw [solutionEnergyNorm_cubeSolutionOfZeroForceDirichlet]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlower hdisc) henergy

/-- Fixed-exponent value estimate for the harmonic lift of a rough boundary
datum.  The coefficient is dimension-only; all scale dependence is confined
to the source lower-ellipticity slot and the datum's inhomogeneous norm. -/
theorem exists_zeroForceDirichlet_datumDifference_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
        (h : H1Function (openCubeSet Q)),
        w.boundaryData = h → 0 < t → t ≤ 1 / 4 →
        ForceBesovRegularity Q (2 * t) h.grad →
          cubeBesovScaleWeight (1 : ℝ) Q *
              cubeLpNorm Q (2 : ℝ≥0∞)
                (fun y ↦ w.toH1.toFun y - h.toFun y) ≤
            C *
              (poincareLowerEllipticityFactor Q a t (.finite 1) *
                  dirichletForcedSolutionEnergyNorm Q a w +
                scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) := by
  let D : ℝ := poincareDiscountFactor (1 / 2 : ℝ) (.finite 1)
  let B : ℝ := boundaryNegativeToL2Factor 1 * Real.sqrt (Fintype.card (Fin d) : ℝ)
  let C : ℝ := boundaryDifferencePriceConst d * (D + B + 1)
  have hD0 : 0 ≤ D := by
    dsimp [D, poincareDiscountFactor]
    exact Real.rpow_nonneg (geometricDiscount_pos (by norm_num)).le _
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (boundaryNegativeToL2Factor_nonneg 1) (Real.sqrt_nonneg _)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (boundaryDifferencePriceConst_pos d) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro Q a t w h hwh ht ht4 hh
  have hmain := cubeBesovScaleWeight_mul_cubeLpNorm_datumDifference_le_negativeBesov
    Q (a := a) (g := fun _ ↦ 0) w (by norm_num : (0 : ℝ) < 1) (by norm_num)
  rw [hwh] at hmain
  have hw := zeroForceDirichlet_negativeBesovTwo_half_le w ht ht4
  have hhneg := cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
    (Q := Q) (s := (1 : ℝ)) (by norm_num) (F := h.grad) h.grad_memVectorL2
  have hhL2 := boundaryNormalizedEuclideanL2_le_positiveBesovNorm hh
  have hhneg' : cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad ≤
      B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
    calc
      cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad ≤
          boundaryNegativeToL2Factor 1 * boundaryNormalizedEuclideanL2 Q h.grad :=
        by simpa using hhneg
      _ ≤ boundaryNegativeToL2Factor 1 *
          (Real.sqrt (Fintype.card (Fin d) : ℝ) *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) :=
        mul_le_mul_of_nonneg_left hhL2 (boundaryNegativeToL2Factor_nonneg 1)
      _ = B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
        dsimp [B]
        ring
  let X : ℝ := poincareLowerEllipticityFactor Q a t (.finite 1) *
    dirichletForcedSolutionEnergyNorm Q a w
  let H : ℝ := scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad
  have hX0 : 0 ≤ X := by
    dsimp [X, poincareLowerEllipticityFactor, dirichletForcedSolutionEnergyNorm,
      h1EnergyNormOnCube]
    exact mul_nonneg
      (Real.rpow_nonneg (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)) _)
      (Real.sqrt_nonneg _)
  have hH0 : 0 ≤ H := by
    dsimp [H, scaleNormalizedPositiveBesovVectorNormTwo]
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hh)
  have hcoef : D * X + B * H ≤ (D + B + 1) * (X + H) := by
    nlinarith [mul_nonneg hD0 hH0, mul_nonneg hB0 hX0,
      mul_nonneg hD0 hX0, mul_nonneg hB0 hH0]
  have hw' : cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) w.toH1.grad ≤
      D * X := by
    simpa only [D, X, mul_assoc] using hw
  calc
    cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun y ↦ w.toH1.toFun y - h.toFun y) ≤
      boundaryDifferencePriceConst d *
        (cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) w.toH1.grad +
          cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad) := hmain
    _ ≤ boundaryDifferencePriceConst d * (D * X + B * H) := by
      apply mul_le_mul_of_nonneg_left _ (boundaryDifferencePriceConst_pos d).le
      exact add_le_add hw' (by simpa [H] using hhneg')
    _ ≤ boundaryDifferencePriceConst d * ((D + B + 1) * (X + H)) :=
      mul_le_mul_of_nonneg_left hcoef (boundaryDifferencePriceConst_pos d).le
    _ = C * (poincareLowerEllipticityFactor Q a t (.finite 1) *
          dirichletForcedSolutionEnergyNorm Q a w +
        scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) := by
      dsimp [C, X, H]
      ring

/-- The mean-zero datum itself has the fixed-exponent value bound needed in
the source normalization step. -/
theorem exists_boundaryDatumFluctuation_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {t : ℝ} (h : H1Function (openCubeSet Q)),
        0 < t → t ≤ 1 / 4 → ForceBesovRegularity Q (2 * t) h.grad →
          cubeBesovScaleWeight (1 : ℝ) Q *
              normalizedL2On (openCubeSet Q)
                (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun) ≤
            C * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
  let G : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 1 / 4)))⁻¹)
  let P : ℝ :=
    (Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) *
      (3 : ℝ) ^ ((d : ℝ) + 1)) * ((d : ℝ) * G)
  let B : ℝ := boundaryNegativeToL2Factor 1 * Real.sqrt (Fintype.card (Fin d) : ℝ)
  let C : ℝ := max 1 (P * B)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left 1 (P * B))
  refine ⟨C, hC, ?_⟩
  intro Q t h ht ht4 hh
  have hmem : MemLp h.toFun 2 (volume.restrict (openCubeSet Q)) := h.memL2
  have hsubmem : MemLp
      (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun) 2
      (volume.restrict (openCubeSet Q)) :=
    h.memL2.sub (memLp_const (volumeAverage (openCubeSet Q) h.toFun))
  have hnorm := normalizedL2On_openCubeSet_eq_cubeLpNorm Q hsubmem
  have havg : volumeAverage (openCubeSet Q) h.toFun = cubeAverage Q h.toFun :=
    volumeAverage_openCubeSet_eq_cubeAverage Q h.toFun
  have hfluct : (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun) =
      cubeFluctuation Q h.toFun := by
    funext y
    simp only [cubeFluctuation, havg]
  have hpoin := cubeBesovScaleWeight_one_mul_cubeLpNorm_fluctuation_le_grad_negativeBesovTwo
    (Q := Q) (t := (1 / 4 : ℝ)) h (by norm_num) (by norm_num)
  have hQconst : Ch01.Legacy.fullVectorPoincareConstant Q =
      Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) := by
    simp [Ch01.Legacy.fullVectorPoincareConstant,
      fullVectorPoincareCubeConstant_eq_dimensionConstant]
  have hpoin' : cubeBesovScaleWeight (1 : ℝ) Q *
      normalizedL2On (openCubeSet Q)
        (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun) ≤
      P * cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad := by
    rw [hnorm, hfluct]
    simpa only [P, G, hQconst, show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num] using hpoin
  have hhneg := cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
    (Q := Q) (s := (1 : ℝ)) (by norm_num) (F := h.grad) h.grad_memVectorL2
  have hhL2 := boundaryNormalizedEuclideanL2_le_positiveBesovNorm hh
  have hP0 : 0 ≤ P := by
    dsimp [P, G]
    exact mul_nonneg
      (mul_nonneg (Ch01.Legacy.fullVectorPoincareConstant_nonneg (originCube d 0))
        (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (boundaryNegativeToL2Factor_nonneg 1) (Real.sqrt_nonneg _)
  have hPB0 : 0 ≤ P * B := by
    exact mul_nonneg hP0 hB0
  have hneg : cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad ≤
      B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
    calc
      _ ≤ boundaryNegativeToL2Factor 1 * boundaryNormalizedEuclideanL2 Q h.grad :=
        by simpa using hhneg
      _ ≤ boundaryNegativeToL2Factor 1 *
          (Real.sqrt (Fintype.card (Fin d) : ℝ) *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) :=
        mul_le_mul_of_nonneg_left hhL2 (boundaryNegativeToL2Factor_nonneg 1)
      _ = B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
        dsimp [B]
        ring
  have hH0 : 0 ≤ scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hh)
  calc
    _ ≤ P * cubeBesovNegativeVectorSeminormTwo Q (1 / 2 : ℝ) h.grad := hpoin'
    _ ≤ P * (B * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad) := by
      exact mul_le_mul_of_nonneg_left hneg hP0
    _ = (P * B) * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad := by ring
    _ ≤ C * scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad :=
      mul_le_mul_of_nonneg_right (le_max_right 1 (P * B)) hH0

/-- The harmonic datum lift's energy, after the fixed lower-ellipticity
factor is inserted, is exactly paid by the printed datum square budget. -/
theorem exists_lambdaS_mul_zeroForceDatumEnergy_sq_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
        (h : H1Function (openCubeSet Q)),
        w.boundaryData = h → 0 < t → t ≤ 1 / 4 →
        ForceBesovRegularity Q (2 * t) h.grad →
          Ch02.lambdaS Q t a *
              (poincareLowerEllipticityFactor Q a t (.finite 1) *
                dirichletForcedSolutionEnergyNorm Q a w) ^ 2 ≤
            C * (Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
              scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := by
  obtain ⟨Ce, hCe, hdir, _⟩ := (energyConsequencesRHSTheory (d := d)).exists_constant
  let C : ℝ := 4 * (25 * Real.exp 4) * max 1 (Ce ^ 2)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_left 1 (Ce ^ 2)))
  refine ⟨C, hC, ?_⟩
  intro Q a t w h hwh ht ht4 hh
  have ht2 : 0 < 2 * t := by linarith
  have ht2one : 2 * t < 1 := by linarith
  have hzero := forceBesovRegularity_zero Q (2 * t)
  have hbg : dirichletBoundaryGradientField w = h.grad := by
    unfold dirichletBoundaryGradientField
    rw [hwh]
  have hh' : ForceBesovRegularity Q (2 * t) (dirichletBoundaryGradientField w) := by
    simpa only [hbg] using hh
  have henergy := hdir (Q := Q) (a := a) (s := 2 * t) (g := fun _ ↦ 0)
    w ht2 ht2one hzero hh'
  have hE0 : 0 ≤ dirichletForcedSolutionEnergyNorm Q a w := by
    unfold dirichletForcedSolutionEnergyNorm h1EnergyNormOnCube
    exact Real.sqrt_nonneg _
  have hEsq : dirichletForcedSolutionEnergyNorm Q a w ^ 2 ≤
      dirichletEnergyWithRHSRHS Ce Q a (2 * t) (fun _ ↦ 0) w ^ 2 :=
    pow_le_pow_left₀ hE0 henergy 2
  have hrough := dirichletEnergyWithRHSRHS_two_mul_sq_le_printed
    (Q := Q) (a := a) (C := Ce) (t := t) (g := fun _ ↦ 0)
    w hCe.le ht ht4 hzero hh'
  have hzeroSemi : scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t)
      (fun _ : Vec d ↦ (0 : Vec d)) = 0 := by
    unfold scaleNormalizedPositiveBesovVectorSeminormTwo
    change cubeBesovPositiveVectorSeminormTwo Q (2 * t)
      (0 : Vec d → Vec d) = 0
    rw [cubeBesovPositiveVectorSeminormTwo_zero]
  have hD : dirichletEnergyWithRHSRHS Ce Q a (2 * t) (fun _ ↦ 0) w ^ 2 ≤
      C * (Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
        scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := by
    rw [hzeroSemi, hbg] at hrough
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add,
      add_zero, C] using hrough
  have hlam : 0 < Ch02.lambdaS Q t a :=
    Ch02.lambdaSq_finite_pos Q a ht (by norm_num)
  have hlowerSq :
      (poincareLowerEllipticityFactor Q a t (.finite 1)) ^ 2 =
        (Ch02.lambdaS Q t a)⁻¹ := by
    unfold poincareLowerEllipticityFactor Ch02.lambdaS
    calc
      (Real.rpow (Ch02.lambdaSq Q t (.finite 1) a) (-(1 / 2 : ℝ))) ^ 2 =
          Real.rpow
            (Real.rpow (Ch02.lambdaSq Q t (.finite 1) a) (-(1 / 2 : ℝ)))
            (2 : ℝ) := (Real.rpow_two _).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (.finite 1) a)
          (-(1 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hlam.le _ _).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (.finite 1) a) (-1 : ℝ) := by norm_num
      _ = (Ch02.lambdaSq Q t (.finite 1) a)⁻¹ := Real.rpow_neg_one _
  calc
    Ch02.lambdaS Q t a *
        (poincareLowerEllipticityFactor Q a t (.finite 1) *
          dirichletForcedSolutionEnergyNorm Q a w) ^ 2 =
      dirichletForcedSolutionEnergyNorm Q a w ^ 2 := by
        rw [mul_pow, hlowerSq]
        field_simp [hlam.ne']
    _ ≤ dirichletEnergyWithRHSRHS Ce Q a (2 * t) (fun _ ↦ 0) w ^ 2 := hEsq
    _ ≤ C * (Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
        scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := hD

omit [NeZero d] in
/-- Exact identification of the weighted cube `L²` square with the scalar
parent carrier used by the Chapter-3 Caccioppoli theorem. -/
theorem lambdaS_mul_weightedCubeLp_sq_eq_parent
    (Q : TriadicCube d) (a : CoeffFamily d) (t : ℝ)
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) :
    Ch02.lambdaS Q t a *
        (cubeBesovScaleWeight (1 : ℝ) Q * cubeLpNorm Q (2 : ℝ≥0∞) f) ^ 2 =
      Ch02.lambdaS Q t a *
        Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
          normalizedL2SqOnSet (openCubeSet Q) f := by
  have hscale : Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) =
      cubeBesovScaleWeight (1 : ℝ) Q ^ 2 := by
    calc
      _ = cubeBesovScaleWeight (2 : ℝ) Q := by
        simpa using publicDualBesovScaleWeight_eq_cubeBesovScaleWeight Q (2 : ℝ)
      _ = cubeBesovScaleWeight (1 : ℝ) Q * cubeBesovScaleWeight (1 : ℝ) Q := by
        rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
        norm_num
      _ = cubeBesovScaleWeight (1 : ℝ) Q ^ 2 := by ring
  have hnorm : cubeLpNorm Q (2 : ℝ≥0∞) f ^ 2 =
      normalizedL2SqOnSet (openCubeSet Q) f := by
    rw [← normalizedL2On_openCubeSet_eq_cubeLpNorm Q hf]
    exact Section6Iteration.normalizedL2On_sq (openCubeSet Q) f
  rw [mul_pow, hnorm, hscale]
  ring

omit [NeZero d] in
private theorem add_sq_le_two_mul_add_sq (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

/-- The normalized parent of the split Dirichlet lift is controlled by the
three source budgets.  This is the quantitative heart of the separate-datum
ASD row. -/
theorem exists_splitDirichlet_parent_le_printedBudgets (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        {g : Vec d → Vec d}
        (rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
        (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0))
        (u h : H1Function (openCubeSet Q)) (c0 : ℝ)
        (hwh : w.boundaryData = h),
        volumeAverage (openCubeSet Q) h.toFun = c0 →
        0 < t → t ≤ 1 / 4 → ForceBesovRegularity Q (2 * t) g →
        ForceBesovRegularity Q (2 * t) h.grad →
          Ch02.lambdaS Q t a *
              Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
              normalizedL2SqOnSet (openCubeSet Q) (fun y ↦
                u.toFun y - (splitDirichletForcedCubeSolution rho w h hwh).toH1.toFun y) ≤
            C *
              (Ch02.lambdaS Q t a *
                  Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                  normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u.toFun y - c0) +
                Real.rpow t (-11 : ℝ) *
                  Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 +
                Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
                  scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := by
  obtain ⟨Kr, hKr, hrho⟩ := zeroTraceCorrectorParentL2_le_forceScale (d := d)
  obtain ⟨Cw, hCw, hwvalue⟩ := exists_zeroForceDirichlet_datumDifference_le d
  obtain ⟨Ce, hCe, hwenergy⟩ := exists_lambdaS_mul_zeroForceDatumEnergy_sq_le d
  obtain ⟨Ch, hCh, hhvalue⟩ := exists_boundaryDatumFluctuation_le d
  let C : ℝ := max 1 (36 + 8 * Kr + 16 * Ch ^ 2 + 32 * Cw ^ 2 * (Ce + 1))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  refine ⟨C, hC, ?_⟩
  intro Q a t g rho w u h c0 hwh hhMean ht ht4 hg hh
  let v := splitDirichletForcedCubeSolution rho w h hwh
  let W := cubeBesovScaleWeight (1 : ℝ) Q
  let U0 := normalizedL2On (openCubeSet Q) (fun y ↦ u.toFun y - c0)
  let H0 := normalizedL2On (openCubeSet Q)
    (fun y ↦ h.toFun y - volumeAverage (openCubeSet Q) h.toFun)
  let R0 := cubeLpNorm Q (2 : ℝ≥0∞)
    (boundaryForcedCaccioppoliCorrectorOpenH10
      (Q := Q) (a := a) rho).toH1Function.toFun
  let V0 := cubeLpNorm Q (2 : ℝ≥0∞) (fun y ↦ w.toH1.toFun y - h.toFun y)
  let X := poincareLowerEllipticityFactor Q a t (.finite 1) *
    dirichletForcedSolutionEnergyNorm Q a w
  let Hn := scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad
  let BU := Ch02.lambdaS Q t a *
    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
    normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u.toFun y - c0)
  let BF := Real.rpow t (-11 : ℝ) *
    Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2
  let BH := Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a * Hn ^ 2
  have hW0 : 0 ≤ W := cubeBesovScaleWeight_nonneg 1 Q
  have hU0 : 0 ≤ U0 := Section6Iteration.normalizedL2On_nonneg _ _
  have hH0 : 0 ≤ H0 := Section6Iteration.normalizedL2On_nonneg _ _
  have hR0 : 0 ≤ R0 := cubeLpNorm_nonneg Q 2 _
  have hV0 : 0 ≤ V0 := cubeLpNorm_nonneg Q 2 _
  have hX0 : 0 ≤ X := by
    dsimp [X, poincareLowerEllipticityFactor, dirichletForcedSolutionEnergyNorm,
      h1EnergyNormOnCube]
    exact mul_nonneg
      (Real.rpow_nonneg (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)) _)
      (Real.sqrt_nonneg _)
  have hHn0 : 0 ≤ Hn := by
    dsimp [Hn, scaleNormalizedPositiveBesovVectorNormTwo]
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hh)
  have hlam0 : 0 ≤ Ch02.lambdaS Q t a :=
    (Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)).le
  have hBU0 : 0 ≤ BU := by
    dsimp [BU]
    exact mul_nonneg
      (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _))
      (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q))
  have hBF0 : 0 ≤ BF := by
    dsimp [BF]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Real.rpow_nonneg hlam0 _)) (sq_nonneg _)
  have hBH0 : 0 ≤ BH := by
    dsimp [BH]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num))) (sq_nonneg _)
  have hsqrt := sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_of_boundaryMean_eq
    Q v u h (by rfl) c0 hhMean
  have hrhoMem : MemLp
      (boundaryForcedCaccioppoliCorrectorOpenH10
        (Q := Q) (a := a) rho).toH1Function.toFun 2
      (normalizedCubeMeasure Q) :=
    (boundaryForcedCaccioppoliCorrectorOpenH10
      (Q := Q) (a := a) rho).toH1Function.memL2_normalizedCubeMeasure
  have hwsubMem : MemLp (fun y ↦ w.toH1.toFun y - h.toFun y) 2
      (normalizedCubeMeasure Q) :=
    w.toH1.memL2_normalizedCubeMeasure.sub h.memL2_normalizedCubeMeasure
  have hvsplit : (fun y ↦ v.toH1.toFun y - h.toFun y) =
      fun y ↦
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) rho).toH1Function.toFun y +
          (w.toH1.toFun y - h.toFun y) := by
    funext y
    dsimp [v]
    ring
  have hvvalue : cubeLpNorm Q (2 : ℝ≥0∞) (fun y ↦ v.toH1.toFun y - h.toFun y) ≤
      R0 + V0 := by
    rw [hvsplit]
    exact cubeLpNorm_add_le Q 2 _ _ hrhoMem hwsubMem (by norm_num)
  have hsqrt' : Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
      (fun y ↦ u.toFun y - v.toH1.toFun y)) ≤ 3 * U0 + H0 + R0 + V0 := by
    dsimp [U0, H0] at hsqrt ⊢
    linarith only [hsqrt, hvvalue]
  have hweighted : W * Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
      (fun y ↦ u.toFun y - v.toH1.toFun y)) ≤
      3 * (W * U0) + W * H0 + W * R0 + W * V0 := by
    have := mul_le_mul_of_nonneg_left hsqrt' hW0
    linarith only [this]
  have hleft0 : 0 ≤ W * Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
      (fun y ↦ u.toFun y - v.toH1.toFun y)) :=
    mul_nonneg hW0 (Real.sqrt_nonneg _)
  have hweightedSq := pow_le_pow_left₀ hleft0 hweighted 2
  have hfour : (3 * (W * U0) + W * H0 + W * R0 + W * V0) ^ 2 ≤
      36 * (W * U0) ^ 2 + 4 * (W * H0) ^ 2 +
        4 * (W * R0) ^ 2 + 4 * (W * V0) ^ 2 := by
    nlinarith [sq_nonneg (3 * (W * U0) - W * H0),
      sq_nonneg (3 * (W * U0) - W * R0),
      sq_nonneg (3 * (W * U0) - W * V0),
      sq_nonneg (W * H0 - W * R0), sq_nonneg (W * H0 - W * V0),
      sq_nonneg (W * R0 - W * V0)]
  have hparentRaw : Ch02.lambdaS Q t a *
      (W * Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
        (fun y ↦ u.toFun y - v.toH1.toFun y))) ^ 2 ≤
      36 * (Ch02.lambdaS Q t a * (W * U0) ^ 2) +
        4 * (Ch02.lambdaS Q t a * (W * H0) ^ 2) +
        4 * (Ch02.lambdaS Q t a * (W * R0) ^ 2) +
        4 * (Ch02.lambdaS Q t a * (W * V0) ^ 2) := by
    have hsq := hweightedSq.trans hfour
    have := mul_le_mul_of_nonneg_left hsq hlam0
    nlinarith only [this]
  have hUident : Ch02.lambdaS Q t a * (W * U0) ^ 2 = BU := by
    have hscaleU : Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) = W ^ 2 := by
      dsimp [W]
      calc
        _ = cubeBesovScaleWeight (2 : ℝ) Q := by
          simpa using publicDualBesovScaleWeight_eq_cubeBesovScaleWeight Q (2 : ℝ)
        _ = cubeBesovScaleWeight (1 : ℝ) Q * cubeBesovScaleWeight (1 : ℝ) Q := by
          rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
          norm_num
        _ = cubeBesovScaleWeight (1 : ℝ) Q ^ 2 := by ring
    have hnormU : U0 ^ 2 = normalizedL2SqOnSet (openCubeSet Q)
        (fun y ↦ u.toFun y - c0) := by
      dsimp [U0, normalizedL2SqOnSet]
      exact Section6Iteration.normalizedL2On_sq (openCubeSet Q)
        (fun y ↦ u.toFun y - c0)
    dsimp only [BU]
    rw [mul_pow, hnormU, ← hscaleU]
    ring
  have hHbound : Ch02.lambdaS Q t a * (W * H0) ^ 2 ≤ Ch ^ 2 * BH := by
    have hhval := hhvalue h ht ht4 hh
    dsimp [W, H0, Hn] at hhval ⊢
    have hsq := pow_le_pow_left₀ (mul_nonneg hW0 hH0) hhval 2
    have hlamUpper := lambdaS_le_LambdaS_local Q a ht ht
    have htOne : t ≤ 1 := by linarith
    have htPow : 1 ≤ Real.rpow t (-3 : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht htOne (by norm_num)
    have hcoeff : Ch02.lambdaS Q t a ≤
        Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a :=
      hlamUpper.trans (by
        calc
          Ch02.LambdaS Q t a = 1 * Ch02.LambdaS Q t a := by ring
          _ ≤ Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a :=
            mul_le_mul_of_nonneg_right htPow
              (Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num)))
    calc
      _ ≤ Ch02.lambdaS Q t a * (Ch * Hn) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hlam0
      _ = Ch ^ 2 * (Ch02.lambdaS Q t a * Hn ^ 2) := by ring
      _ ≤ Ch ^ 2 * (Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a * Hn ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg Hn)) (sq_nonneg Ch)
  have hrhoRaw := hrho rho ht (by linarith only [ht4]) hg
  have hpole := rpow_neg_eight_div_one_sub_two_mul_le_two_mul_rpow_neg_eleven ht ht4
  have hrhoBound : Ch02.lambdaS Q t a * (W * R0) ^ 2 ≤ 2 * Kr * BF := by
    have hrhoOpen : MemLp
        (boundaryForcedCaccioppoliCorrectorOpenH10
          (Q := Q) (a := a) rho).toH1Function.toFun 2
        (volume.restrict (openCubeSet Q)) :=
      (boundaryForcedCaccioppoliCorrectorOpenH10
        (Q := Q) (a := a) rho).toH1Function.memL2
    rw [lambdaS_mul_weightedCubeLp_sq_eq_parent Q a t _ hrhoOpen]
    have htail : 0 ≤ Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hlam0 _) (sq_nonneg _)
    calc
      _ ≤ Kr * ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          (Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2)) := by
        simpa only [mul_assoc] using hrhoRaw
      _ ≤ Kr * ((2 * Real.rpow t (-11 : ℝ)) *
          (Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpole htail) hKr.le
      _ = 2 * Kr * BF := by dsimp [BF]; ring
  have hwval := hwvalue w h hwh ht ht4 hh
  have hwvalSq : (W * V0) ^ 2 ≤ Cw ^ 2 * 2 * (X ^ 2 + Hn ^ 2) := by
    have hwval' : W * V0 ≤ Cw * (X + Hn) := by
      simpa only [W, V0, X, Hn] using hwval
    have hsq := pow_le_pow_left₀ (mul_nonneg hW0 hV0) hwval' 2
    calc
      _ ≤ (Cw * (X + Hn)) ^ 2 := hsq
      _ = Cw ^ 2 * (X + Hn) ^ 2 := by ring
      _ ≤ Cw ^ 2 * (2 * (X ^ 2 + Hn ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (add_sq_le_two_mul_add_sq X Hn) (sq_nonneg Cw)
      _ = Cw ^ 2 * 2 * (X ^ 2 + Hn ^ 2) := by ring
  have hX := hwenergy w h hwh ht ht4 hh
  have hlamUpper := lambdaS_le_LambdaS_local Q a ht ht
  have htOne : t ≤ 1 := by linarith
  have htPow : 1 ≤ Real.rpow t (-3 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht htOne (by norm_num)
  have hlamH : Ch02.lambdaS Q t a * Hn ^ 2 ≤ BH := by
    dsimp [BH]
    have hcoeff : Ch02.lambdaS Q t a ≤
        Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a :=
      hlamUpper.trans (by
        calc
          Ch02.LambdaS Q t a = 1 * Ch02.LambdaS Q t a := by ring
          _ ≤ Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a :=
            mul_le_mul_of_nonneg_right htPow
              (Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num)))
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg Hn)
  have hwBound : Ch02.lambdaS Q t a * (W * V0) ^ 2 ≤
      2 * Cw ^ 2 * (Ce + 1) * BH := by
    calc
      _ ≤ Ch02.lambdaS Q t a * (Cw ^ 2 * 2 * (X ^ 2 + Hn ^ 2)) :=
        mul_le_mul_of_nonneg_left hwvalSq hlam0
      _ = 2 * Cw ^ 2 *
          (Ch02.lambdaS Q t a * X ^ 2 + Ch02.lambdaS Q t a * Hn ^ 2) := by ring
      _ ≤ 2 * Cw ^ 2 * (Ce * BH + BH) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hX hlamH)
          (mul_nonneg (by norm_num) (sq_nonneg Cw))
      _ = 2 * Cw ^ 2 * (Ce + 1) * BH := by ring
  have hsum :
      36 * (Ch02.lambdaS Q t a * (W * U0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * H0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * R0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * V0) ^ 2) ≤
        (36 + 8 * Kr + 16 * Ch ^ 2 + 32 * Cw ^ 2 * (Ce + 1)) *
          (BU + BF + BH) := by
    let Ktot : ℝ := 36 + 8 * Kr + 16 * Ch ^ 2 + 32 * Cw ^ 2 * (Ce + 1)
    have hKr0 : 0 ≤ Kr := hKr.le
    have hCe1 : 0 ≤ Ce + 1 := by linarith only [hCe]
    have hChSq : 0 ≤ Ch ^ 2 := sq_nonneg Ch
    have hCwCe : 0 ≤ Cw ^ 2 * (Ce + 1) := mul_nonneg (sq_nonneg Cw) hCe1
    have hcoefU : 36 ≤ Ktot := by
      dsimp [Ktot]
      linarith only [hKr0, hChSq, hCwCe]
    have hcoefF : 8 * Kr ≤ Ktot := by
      dsimp [Ktot]
      linarith only [hChSq, hCwCe]
    have hcoefH : 4 * Ch ^ 2 + 8 * Cw ^ 2 * (Ce + 1) ≤ Ktot := by
      dsimp [Ktot]
      linarith only [hKr0, hChSq, hCwCe]
    calc
      36 * (Ch02.lambdaS Q t a * (W * U0) ^ 2) +
            4 * (Ch02.lambdaS Q t a * (W * H0) ^ 2) +
            4 * (Ch02.lambdaS Q t a * (W * R0) ^ 2) +
            4 * (Ch02.lambdaS Q t a * (W * V0) ^ 2) ≤
          36 * BU + 4 * (Ch ^ 2 * BH) + 4 * (2 * Kr * BF) +
            4 * (2 * Cw ^ 2 * (Ce + 1) * BH) := by
        exact add_le_add
          (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left (le_of_eq hUident) (by norm_num))
            (mul_le_mul_of_nonneg_left hHbound (by norm_num)))
            (mul_le_mul_of_nonneg_left hrhoBound (by norm_num)))
          (mul_le_mul_of_nonneg_left hwBound (by norm_num))
      _ = 36 * BU + (8 * Kr) * BF +
          (4 * Ch ^ 2 + 8 * Cw ^ 2 * (Ce + 1)) * BH := by ring
      _ ≤ Ktot * BU + Ktot * BF + Ktot * BH := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hcoefU hBU0)
            (mul_le_mul_of_nonneg_right hcoefF hBF0))
          (mul_le_mul_of_nonneg_right hcoefH hBH0)
      _ = Ktot * (BU + BF + BH) := by ring
  have hscale : Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) = W ^ 2 := by
    dsimp [W]
    calc
      _ = cubeBesovScaleWeight (2 : ℝ) Q := by
        simpa using publicDualBesovScaleWeight_eq_cubeBesovScaleWeight Q (2 : ℝ)
      _ = cubeBesovScaleWeight (1 : ℝ) Q * cubeBesovScaleWeight (1 : ℝ) Q := by
        rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
        norm_num
      _ = cubeBesovScaleWeight (1 : ℝ) Q ^ 2 := by ring
  have hsqrtSq : (Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
      (fun y ↦ u.toFun y - v.toH1.toFun y))) ^ 2 =
      normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u.toFun y - v.toH1.toFun y) :=
    Real.sq_sqrt (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q))
  have hbudget0 : 0 ≤ BU + BF + BH := by linarith only [hBU0, hBF0, hBH0]
  calc
    _ = Ch02.lambdaS Q t a *
        (W * Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
          (fun y ↦ u.toFun y - v.toH1.toFun y))) ^ 2 := by
      rw [mul_pow, hsqrtSq, ← hscale]
      ring
    _ ≤ 36 * (Ch02.lambdaS Q t a * (W * U0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * H0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * R0) ^ 2) +
          4 * (Ch02.lambdaS Q t a * (W * V0) ^ 2) := hparentRaw
    _ ≤ (36 + 8 * Kr + 16 * Ch ^ 2 + 32 * Cw ^ 2 * (Ce + 1)) *
          (BU + BF + BH) := hsum
    _ ≤ C * (BU + BF + BH) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 _) hbudget0



theorem exists_boundary_caccioppoli_quarter_with_datum
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        {x : Vec d} {g : Vec d → Vec d}
        (u h : H1Function (openCubeSet Q)) (c₀ : ℝ),
        IsForcedEquation Q a u g →
        Ch01.LocalizedZeroTraceFunctionOn
          (openCubeSet Q) (openCubeAtScale x (Q.scale - 1))
          (fun y ↦ u.toFun y - h.toFun y) →
        volumeAverage (openCubeSet Q) h.toFun = c₀ →
        0 < s → s < 1 → 0 < t → t ≤ 1 / 4 → s + t < 1 →
        x ∈ openCubeSet Q →
        ForceBesovRegularity Q (2 * t) g →
        ForceBesovRegularity Q (2 * t) h.grad →
        localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
          caccioppoliWithRHSPrefactor C Q a s t *
            (Ch02.lambdaS Q t a *
                Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y ↦ u.toFun y - c₀) +
              Real.rpow t (-11 : ℝ) *
                Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 +
              Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
                scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hcacc⟩ :=
    exists_boundaryCaccioppoliEnergy_withBoundaryDatum d
  obtain ⟨Kp, hKp, hparent⟩ := exists_splitDirichlet_parent_le_printedBudgets d
  let Kd : ℝ := 4 * (25 * Real.exp 4) * max 1 (C₂ ^ 2)
  let Md : ℝ := 2 * (18 : ℝ) ^ d * Kd
  let M : ℝ := max 1 (2 * Kp + Md)
  let Cb : ℝ := max 1 C₁
  let C : ℝ := M * Cb
  have hKd0 : 0 ≤ Kd := by
    dsimp [Kd]
    positivity
  have hMd0 : 0 ≤ Md := by
    dsimp [Md]
    positivity
  have hM : 1 ≤ M := le_max_left _ _
  have hCb : 1 ≤ Cb := le_max_left _ _
  have hC : 0 < C := mul_pos (lt_of_lt_of_le zero_lt_one hM)
    (lt_of_lt_of_le zero_lt_one hCb)
  refine ⟨C, hC, ?_⟩
  intro Q a s t x g u h c₀ hu htrace hhMean hs hs₁ ht ht₄ hst hx hg hh
  have ht₂ : 2 * t < 1 := by linarith
  have hgL2 : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_forceBesovRegularity hg
  let rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g :=
    zeroTraceDirichletCorrectorData_publicCoeffField Q a hgL2
  have hzeroL2 : MemVectorL2 (openCubeSet Q) (fun _ ↦ (0 : Vec d)) := by
    rw [MemVectorL2, volumeMeasureOn]
    exact MemLp.zero
  obtain ⟨w, hwh, rw, hrwValue, _hrwGrad⟩ :=
    exists_dirichletForcedCubeSolution_boundaryData_withGradient Q a h hzeroL2
  let v : DirichletForcedCubeSolution Q a g :=
    splitDirichletForcedCubeSolution rho w h hwh
  let r₀ : H10Function (openCubeSet Q) :=
    boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) rho
  have hvhPoint : ∀ y,
      (r₀ + rw).toH1Function.toFun y = v.toH1.toFun y - h.toFun y := by
    intro y
    change r₀.toH1Function.toFun y + rw.toH1Function.toFun y = _
    rw [hrwValue y]
    dsimp [v, r₀]
    ring
  have hvhTrace : Ch01.LocalizedZeroTraceFunctionOn
      (openCubeSet Q) (openCubeAtScale x (Q.scale - 1))
      (fun y ↦ v.toH1.toFun y - h.toFun y) :=
    Section6SchauderDatum.localizedZeroTraceFunctionOn_of_memH10
      ⟨r₀ + rw, funext hvhPoint⟩
  have huvTraceRaw := Homogenization.localizedZeroTraceFunctionOn_sub htrace hvhTrace
  have huvTrace : Ch01.LocalizedZeroTraceFunctionOn
      (openCubeSet Q) (openCubeAtScale x (Q.scale - 1))
      (fun y ↦ u.toFun y - v.toH1.toFun y) :=
    Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun y ↦ by ring) huvTraceRaw
  have hzeroReg : ForceBesovRegularity Q (2 * t) (fun _ ↦ (0 : Vec d)) :=
    forceBesovRegularity_zero Q (2 * t)
  have hvBoundary : dirichletBoundaryGradientField v = h.grad := by
    unfold dirichletBoundaryGradientField
    rfl
  have hvBoundaryReg : ForceBesovRegularity Q (2 * t)
      (dirichletBoundaryGradientField v) := by
    simpa only [hvBoundary] using hh
  have hraw := hcacc u v hu huvTrace hs hs₁ ht (by linarith only [ht₄]) hst
    (by positivity : 0 < 2 * t) ht₂ hg hvBoundaryReg hx
  have hp := hparent (rho := rho) (w := w) (u := u) (h := h) c₀ hwh
    hhMean ht ht₄ hg hh
  have hd := dirichletEnergyWithRHSRHS_two_mul_sq_le_printed
    (Q := Q) (a := a) (C := C₂) (t := t) (g := g) v hC₂.le ht ht₄ hg
      hvBoundaryReg
  let BU : ℝ := Ch02.lambdaS Q t a *
    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
    normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u.toFun y - c₀)
  let BF : ℝ := Real.rpow t (-11 : ℝ) *
    Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2
  let BH : ℝ := Real.rpow t (-3 : ℝ) * Ch02.LambdaS Q t a *
    scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2
  let B : ℝ := BU + BF + BH
  let P₁ : ℝ := caccioppoliWithRHSPrefactor Cb Q a s t
  have hlam0 : 0 ≤ Ch02.lambdaS Q t a :=
    (Ch02.lambdaSq_finite_pos Q a ht (by norm_num)).le
  have hBU0 : 0 ≤ BU := by
    dsimp [BU]
    exact mul_nonneg
      (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _))
      (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q))
  have hBF0 : 0 ≤ BF := by
    dsimp [BF]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Real.rpow_nonneg hlam0 _)) (sq_nonneg _)
  have hBH0 : 0 ≤ BH := by
    dsimp [BH]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num))) (sq_nonneg _)
  have hB0 : 0 ≤ B := by dsimp [B]; linarith only [hBU0, hBF0, hBH0]
  have hP₁ : 1 ≤ P₁ := by
    dsimp [P₁]
    exact one_le_caccioppoliWithRHSPrefactor hCb hs hs₁ ht hst
  have hP₁nonneg : 0 ≤ P₁ := le_trans zero_le_one hP₁
  have hprefBase : caccioppoliWithRHSPrefactor C₁ Q a s t ≤ P₁ := by
    have hmono := caccioppoliWithRHSPrefactor_mul_const_le_of_mul_constant_le
      (M := (1 : ℝ)) (C₁ := C₁) (C₂ := Cb) (Q := Q) (a := a)
      (s := s) (t := t) (by norm_num) hC₁.le (by
        dsimp [Cb]
        simpa only [one_mul] using (le_max_right (1 : ℝ) C₁))
      hs ht hst
    simpa only [one_mul, P₁] using hmono
  have hp' : Ch02.lambdaS Q t a *
        Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
        normalizedL2SqOnSet (openCubeSet Q)
          (fun y ↦ u.toFun y - v.toH1.toFun y) ≤ Kp * B := by
    simpa only [BU, BF, BH, B] using hp
  have hd' : dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2 ≤
      Kd * (BF + BH) := by
    rw [hvBoundary] at hd
    simpa only [Kd, BF, BH] using hd
  have hdB : dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2 ≤ Kd * B := by
    calc
      _ ≤ Kd * (BF + BH) := hd'
      _ ≤ Kd * B := by
        apply mul_le_mul_of_nonneg_left _ hKd0
        dsimp [B]
        linarith only [hBU0]
  have hscalePow : (3 : ℝ) ^ (-(2 * Q.scale)) =
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) := by
    rw [← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hfirst : 2 * (P₁ *
      (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
        normalizedL2SqOnSet (openCubeSet Q)
          (fun y ↦ u.toFun y - v.toH1.toFun y))) ≤
      (2 * Kp) * P₁ * B := by
    rw [hscalePow]
    have htwoP : 0 ≤ (2 : ℝ) * P₁ :=
      mul_nonneg (by norm_num) hP₁nonneg
    calc
      _ = (2 * P₁) *
          (Ch02.lambdaS Q t a * Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y ↦ u.toFun y - v.toH1.toFun y)) := by ring
      _ ≤ (2 * P₁) * (Kp * B) := mul_le_mul_of_nonneg_left hp' htwoP
      _ = (2 * Kp) * P₁ * B := by ring
  have hsecond : 2 * ((18 : ℝ) ^ d *
      dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2) ≤
      Md * P₁ * B := by
    calc
      _ = (2 * (18 : ℝ) ^ d) *
          dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2 := by ring
      _ ≤ (2 * (18 : ℝ) ^ d) * (Kd * B) :=
        mul_le_mul_of_nonneg_left hdB (by positivity)
      _ = Md * B := by dsimp [Md]; ring
      _ ≤ Md * P₁ * B := by
        have hBP : B ≤ P₁ * B := by
          calc B = 1 * B := by ring
               _ ≤ P₁ * B := mul_le_mul_of_nonneg_right hP₁ hB0
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hBP hMd0
  have htoM : (2 * Kp) * P₁ * B + Md * P₁ * B ≤ M * P₁ * B := by
    have hcoef : 2 * Kp + Md ≤ M := le_max_right 1 _
    calc
      _ = (2 * Kp + Md) * (P₁ * B) := by ring
      _ ≤ M * (P₁ * B) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hP₁nonneg hB0)
      _ = M * P₁ * B := by ring
  have hpref : M * P₁ ≤ caccioppoliWithRHSPrefactor C Q a s t := by
    dsimp [P₁, C]
    exact caccioppoliWithRHSPrefactor_mul_const_le_of_mul_constant_le
      hM (le_trans zero_le_one hCb) le_rfl hs ht hst
  have hparentCarrier0 : 0 ≤ Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
      normalizedL2SqOnSet (openCubeSet Q)
        (fun y ↦ u.toFun y - v.toH1.toFun y) := by
    exact mul_nonneg
      (mul_nonneg hlam0 (by positivity))
      (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q))
  calc
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
        2 * (P₁ *
          (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y ↦ u.toFun y - v.toH1.toFun y))) +
          2 * ((18 : ℝ) ^ d *
            dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2) := by
      calc
        _ ≤ 2 * (caccioppoliWithRHSPrefactor C₁ Q a s t *
              (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y ↦ u.toFun y - v.toH1.toFun y))) +
            2 * ((18 : ℝ) ^ d *
              dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2) := hraw
        _ ≤ 2 * (P₁ *
              (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y ↦ u.toFun y - v.toH1.toFun y))) +
            2 * ((18 : ℝ) ^ d *
              dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hprefBase hparentCarrier0) (by norm_num)) le_rfl
    _ ≤ (2 * Kp) * P₁ * B + Md * P₁ * B := add_le_add hfirst hsecond
    _ ≤ M * P₁ * B := htoM
    _ ≤ caccioppoliWithRHSPrefactor C Q a s t * B :=
      mul_le_mul_of_nonneg_right hpref hB0
    _ = caccioppoliWithRHSPrefactor C Q a s t * (BU + BF + BH) := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
