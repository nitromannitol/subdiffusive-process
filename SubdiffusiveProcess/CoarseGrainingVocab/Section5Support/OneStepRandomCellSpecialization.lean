module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepQuarterBesovInterpolation
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionVector

@[expose] public section




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A single coordinate's depth-zero Besov seminorm is controlled uniformly
in the depth by twice the parent normalized vector `L²` norm. -/
theorem oneStep_cubeBesovDepthSeminorm_zero_gradCoord_le
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (i : Fin d) (j : ℕ) :
    cubeBesovDepthSeminorm Q 0 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) u.grad := by
  have hu : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q u.grad_memVectorL2
  have hlocal : ∀ R ∈ descendantsAtDepth Q j,
      cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R u.grad) ≤
        2 * cubeLpNorm R (2 : ℝ≥0∞) u.grad := by
    intro R hR
    exact cubeLpNorm_two_cubeFluctuationVec_le_two_mul_cubeLpNorm_two R u.grad
      (memLp_on_descendant_of_memLp_generic hR hu)
  have havg : cubeBesovPositiveVectorDepthAverage Q u.grad j ≤
      4 * descendantsAverage Q j
        (fun R => (cubeLpNorm R (2 : ℝ≥0∞) u.grad) ^ 2) := by
    unfold cubeBesovPositiveVectorDepthAverage
    calc
      descendantsAverage Q j
          (fun R => cubeLpNorm R (2 : ℝ≥0∞)
            (cubeFluctuationVec R u.grad) ^ 2) ≤
          descendantsAverage Q j
            (fun R => (2 * cubeLpNorm R (2 : ℝ≥0∞) u.grad) ^ 2) := by
        refine descendantsAverage_le_descendantsAverage Q j ?_
        intro R hR
        have hleft := cubeLpNorm_nonneg R (2 : ℝ≥0∞)
          (cubeFluctuationVec R u.grad)
        have hright := cubeLpNorm_nonneg R (2 : ℝ≥0∞) u.grad
        nlinarith [hlocal R hR]
      _ = 4 * descendantsAverage Q j
          (fun R => (cubeLpNorm R (2 : ℝ≥0∞) u.grad) ^ 2) := by
        rw [← descendantsAverage_mul_left]
        congr 1
        funext R
        ring
  have hpartition := descendantsAverage_cubeLpNorm_two_sq_eq_cubeLpNorm_two_sq
    Q u.grad j hu
  have hcomponent := cubeBesovDepthAverage_two_component_le_positiveVectorDepthAverage
    Q u.grad i j hu
  have hroot :
      (cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x => u.grad x i) j) ^
          (1 / 2 : ℝ) ≤ 2 * cubeLpNorm Q (2 : ℝ≥0∞) u.grad := by
    have htotal : cubeBesovDepthAverage Q (2 : ℝ≥0∞)
        (fun x => u.grad x i) j ≤
        4 * (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) ^ 2 := by
      calc
        _ ≤ cubeBesovPositiveVectorDepthAverage Q u.grad j := hcomponent
        _ ≤ 4 * descendantsAverage Q j
            (fun R => (cubeLpNorm R (2 : ℝ≥0∞) u.grad) ^ 2) := havg
        _ = 4 * (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) ^ 2 := by rw [hpartition]
    have hleft0 := cubeBesovDepthAverage_nonneg Q (2 : ℝ≥0∞)
      (fun x => u.grad x i) j
    have hnorm0 := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u.grad
    rw [← Real.sqrt_eq_rpow]
    have hsqrtSq := Real.sq_sqrt hleft0
    have hsqrt0 := Real.sqrt_nonneg
      (cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x => u.grad x i) j)
    nlinarith
  simpa [cubeBesovDepthSeminorm, cubeBesovDepthWeight] using hroot

/-- The dimension-only constant used by the literal quarter-order cell
specialization. -/
def oneStepQuarterCellConst (d : ℕ) : ℝ :=
  max 2 (originCubeMeanZeroH1CoerciveEstimate d 0).constant

theorem oneStepQuarterCellConst_pos (d : ℕ) :
    0 < oneStepQuarterCellConst d :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)



theorem oneStep_cubeBesovPartialSeminormTop_cubeFluctuation_eq
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → ℝ) (N : ℕ)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N (cubeFluctuation Q u) =
      cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N u := by
  have hdepth : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (cubeFluctuation Q u) j =
        cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j := by
    intro j
    have havg : cubeBesovDepthAverage Q (2 : ℝ≥0∞)
        (cubeFluctuation Q u) j =
        cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j := by
      unfold cubeBesovDepthAverage descendantsAverage
      simp only
      congr 1
      apply Finset.sum_congr rfl
      intro R hR
      rw [cubeBesovOscillation_cubeFluctuation_eq_of_memLp_two R Q
        (memLp_on_descendant_of_memLp_generic hR hu)]
    unfold cubeBesovDepthSeminorm
    rw [havg]
  unfold cubeBesovPartialSeminormTop
  congr 1
  funext j
  exact hdepth j

/-- The literal positive `B^(1/4)_(2,infinity)` estimate for one coordinate
of a random-cell gradient.  Its two source observables have the same physical
units: the normalized parent `L²` size and `side(Q)` times the normalized weak
Hessian size. -/
theorem oneStep_gradient_cubeBesovPartialSeminormTop_quarter_le
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (N : ℕ) :
    cubeBesovPartialSeminormTop Q (1 / 4 : ℝ) (2 : ℝ≥0∞) N
        (fun x => u.grad x i) ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) Q * oneStepQuarterCellConst d *
        oneStepCellBesovSize
          (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) (oneStepCellB Q H) := by
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) u.grad
  let B : ℝ := oneStepCellB Q H
  let C : ℝ := oneStepQuarterCellConst d
  have hA : 0 ≤ A := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u.grad
  have hB : 0 ≤ B := oneStepCellB_nonneg Q H
  have hC : 0 ≤ C := (oneStepQuarterCellConst_pos d).le
  apply oneStep_cubeBesovPartialSeminormTop_quarter_le_normalized
    Q (fun x => u.grad x i) N hA hB hC
  · intro j
    have hzero := oneStep_cubeBesovDepthSeminorm_zero_gradCoord_le Q u i j
    have h2C : (2 : ℝ) ≤ C := le_max_left _ _
    have hAle : 2 * A ≤ C * A := mul_le_mul_of_nonneg_right h2C hA
    have hs0 : cubeBesovDepthSeminorm Q 0 (2 : ℝ≥0∞)
        (fun x => u.grad x i) j ≤ C * A := hzero.trans hAle
    let rho : ℝ := (3 : ℝ)⁻¹ ^ j
    let D : ℝ := (cubeBesovDepthAverage Q (2 : ℝ≥0∞)
      (fun x => u.grad x i) j) ^ (1 / 2 : ℝ)
    have hrho : 0 < rho := by dsimp [rho]; positivity
    have hscaleQ : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    have hs0' : D ≤ C * A := by
      simpa [cubeBesovDepthSeminorm, cubeBesovDepthWeight, rho, D] using hs0
    change (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-(1 / 4 : ℝ)) * D ≤
      (cubeBesovScaleWeight (1 / 4 : ℝ) Q * C) * A *
        (Real.sqrt (Real.sqrt rho))⁻¹
    rw [show cubeScaleFactor Q / (3 : ℝ) ^ j = cubeScaleFactor Q * rho by
      simp [rho, div_eq_mul_inv], Real.mul_rpow hscaleQ.le hrho.le,
      Real.rpow_neg hscaleQ.le, Real.rpow_neg hrho.le]
    have hr : rho ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt rho) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hrho.le]
      norm_num
    rw [hr]
    unfold cubeBesovScaleWeight
    have hfactor : 0 ≤ (cubeScaleFactor Q ^ (1 / 4 : ℝ))⁻¹ *
        (Real.sqrt (Real.sqrt rho))⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_left hs0' hfactor
    convert hmul using 1
    all_goals rw [Real.rpow_neg hscaleQ.le]
    all_goals ring
  · intro j
    have hone := H.cubeBesovDepthSeminorm_gradCoord_le_parentVolume_scaledCoercive i j
    have hC0C : (originCubeMeanZeroH1CoerciveEstimate d 0).constant ≤ C :=
      le_max_right _ _
    have hnorm : 0 ≤ oneStepCellNormalizedHessianSize Q H :=
      oneStepCellNormalizedHessianSize_nonneg Q H
    have hone' : cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
        (fun x => u.grad x i) j ≤ C * oneStepCellNormalizedHessianSize Q H := by
      calc
        _ ≤ (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
              (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
              H.hessianCoordL2NormSum := hone
        _ = (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
              oneStepCellNormalizedHessianSize Q H := by
              unfold oneStepCellNormalizedHessianSize
              ring
        _ ≤ C * oneStepCellNormalizedHessianSize Q H :=
              mul_le_mul_of_nonneg_right hC0C hnorm
    let rho : ℝ := (3 : ℝ)⁻¹ ^ j
    let D : ℝ := (cubeBesovDepthAverage Q (2 : ℝ≥0∞)
      (fun x => u.grad x i) j) ^ (1 / 2 : ℝ)
    have hrho : 0 < rho := by dsimp [rho]; positivity
    have hscaleQ : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    have honeD : (cubeScaleFactor Q * rho) ^ (-1 : ℝ) * D ≤
        C * oneStepCellNormalizedHessianSize Q H := by
      rw [cubeBesovDepthSeminorm, cubeBesovDepthWeight] at hone'
      simpa only [show cubeScaleFactor Q / (3 : ℝ) ^ j =
        cubeScaleFactor Q * rho by simp [rho, div_eq_mul_inv], D] using! hone'
    let factor : ℝ := cubeScaleFactor Q ^ (3 / 4 : ℝ) * rho ^ (3 / 4 : ℝ)
    have hmul := mul_le_mul_of_nonneg_left honeD
      (by dsimp [factor]; positivity : 0 ≤ factor)
    change (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-(1 / 4 : ℝ)) * D ≤
      (cubeBesovScaleWeight (1 / 4 : ℝ) Q * C) * B *
        Real.sqrt (rho * Real.sqrt rho)
    have hrthree : Real.sqrt (rho * Real.sqrt rho) = rho ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [Real.mul_rpow hrho.le (Real.rpow_nonneg hrho.le _),
        ← Real.rpow_mul hrho.le, ← Real.rpow_add hrho]
      norm_num
    rw [show cubeScaleFactor Q / (3 : ℝ) ^ j = cubeScaleFactor Q * rho by
      simp [rho, div_eq_mul_inv], Real.mul_rpow hscaleQ.le hrho.le,
      Real.rpow_neg hscaleQ.le, Real.rpow_neg hrho.le, hrthree]
    unfold cubeBesovScaleWeight B oneStepCellB
    have hleftFactor : factor * ((cubeScaleFactor Q * rho) ^ (-1 : ℝ) * D) =
        cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) *
          rho ^ (-(1 / 4 : ℝ)) * D := by
      dsimp [factor]
      rw [Real.mul_rpow hscaleQ.le hrho.le]
      calc
        cubeScaleFactor Q ^ (3 / 4 : ℝ) * rho ^ (3 / 4 : ℝ) *
            (cubeScaleFactor Q ^ (-1 : ℝ) * rho ^ (-1 : ℝ) * D) =
            (cubeScaleFactor Q ^ (3 / 4 : ℝ) *
              cubeScaleFactor Q ^ (-1 : ℝ)) *
            (rho ^ (3 / 4 : ℝ) * rho ^ (-1 : ℝ)) * D := by ring
        _ = cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) *
              rho ^ (-(1 / 4 : ℝ)) * D := by
          rw [← Real.rpow_add hscaleQ, ← Real.rpow_add hrho]
          norm_num
    have hrightFactor : factor *
          (C * oneStepCellNormalizedHessianSize Q H) =
        cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) * C *
          (cubeScaleFactor Q * oneStepCellNormalizedHessianSize Q H) *
          rho ^ (3 / 4 : ℝ) := by
      dsimp [factor]
      calc
        cubeScaleFactor Q ^ (3 / 4 : ℝ) * rho ^ (3 / 4 : ℝ) *
            (C * oneStepCellNormalizedHessianSize Q H) =
            (cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) *
              cubeScaleFactor Q) * C *
              oneStepCellNormalizedHessianSize Q H * rho ^ (3 / 4 : ℝ) := by
          rw [show cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) * cubeScaleFactor Q =
              cubeScaleFactor Q ^ (3 / 4 : ℝ) by
            calc
              cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) * cubeScaleFactor Q =
                  cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) *
                    cubeScaleFactor Q ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = cubeScaleFactor Q ^ (-(1 / 4 : ℝ) + 1) :=
                    Real.rpow_add hscaleQ _ _ |>.symm
              _ = cubeScaleFactor Q ^ (3 / 4 : ℝ) := by norm_num]
          ring
        _ = _ := by ring
    rw [hleftFactor, hrightFactor] at hmul
    simpa only [Real.rpow_neg hscaleQ.le, Real.rpow_neg hrho.le] using hmul

/-- The preceding literal gradient estimate in the exact dual-test form
consumed by the localized `q = 1` energy inequality. -/
theorem oneStep_gradient_qOne_dualTest_quarter_le
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (N : ℕ) :
    cubeBesovDualTestNorm Q (1 / 4 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => cubeFluctuationVec Q u.grad x i) ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) Q *
        (oneStepQuarterCellConst d * oneStepCellBesovSize
          (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) (oneStepCellB Q H)) := by
  have hu : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q u.grad_memVectorL2
  apply oneStep_qOne_dualTest_of_positiveTop_component_bounds Q u.grad
  intro k K
  have hmain := oneStep_gradient_cubeBesovPartialSeminormTop_quarter_le
    Q u H k K
  rw [← cubeFluctuation_component_eq_cubeFluctuationVec_component Q u.grad k,
    oneStep_cubeBesovPartialSeminormTop_cubeFluctuation_eq Q
      (1 / 4 : ℝ) (fun x => u.grad x k) K
      (memLp_component_of_memLp u.grad k hu)]
  simpa only [mul_assoc] using hmain

/-! ## Insertion into the localized cell minimizers -/

/-- The literal quarter-order gradient specialization inserted into the
Dirichlet cell energy argument.  The negative-norm premise is kept explicit:
in the GMC application it is supplied by the translated-cube coarse Poincare
theorem.  All positive-Besov and interpolation premises have disappeared. -/
theorem OneStepDirichletCellMinimizer.energy_le_of_gradient_quarter
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (X : OneStepDirichletCellMinimizer Q a u.grad)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {ellipticity : ℝ} (hell : 0 ≤ ellipticity)
    (hcenter : cubeAverageVec Q u.grad = 0)
    (hflux : MemLp (fun x ↦ matVecMul (a x) (X.field x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q (1 / 4 : ℝ) N
          (fun x ↦ matVecMul (a x) (X.field x)) ≤
        Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.field x) (matVecMul (a x) (X.field x))))) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.field x) (matVecMul (a x) (X.field x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          oneStepQuarterCellConst d) ^ 2 * ellipticity *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) (oneStepCellB Q H) := by
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) u.grad
  let B : ℝ := oneStepCellB Q H
  let C : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))
  let D : ℝ := oneStepQuarterCellConst d
  have hA : 0 ≤ A := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u.grad
  have hB : 0 ≤ B := oneStepCellB_nonneg Q H
  have hD : 0 ≤ D := (oneStepQuarterCellConst_pos d).le
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (by norm_num) _)
  have hCD : 0 ≤ C * D := by
    exact mul_nonneg hC hD
  have hu : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
      u.grad_memVectorL2
  have hpairRaw := oneStep_abs_volumeAverage_pairing_le_of_qOne_besov_bounds
    Q (fun x ↦ matVecMul (a x) (X.field x)) u.grad
      (by norm_num : (0 : ℝ) < 1 / 4) hflux hu hcenter
      (mul_nonneg hD (oneStepCellBesovSize_nonneg hA hB)) hneg
      (fun i N ↦ by
        simpa only [A, B, D, mul_assoc] using
          oneStep_gradient_qOne_dualTest_quarter_le Q u H i N)
  have hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (u.grad x) (matVecMul (a x) (X.field x)))| ≤
        (C * D) * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.field x) (matVecMul (a x) (X.field x)))) *
          oneStepCellBesovSize A B := by
    dsimp only [C] at hpairRaw ⊢
    calc
      _ ≤ _ := hpairRaw
      _ = _ := by ring
  simpa only [A, B, C, D] using
    X.energy_le_two_mul_cellBesovError hEll u.grad_memVectorL2
      hCD hell hA hB hpair

/-- Dual counterpart of
`OneStepDirichletCellMinimizer.energy_le_of_gradient_quarter`.  It removes the
positive-Besov premise for the centered Neumann datum and leaves only the
translated coarse-Poincare estimate for the selected potential gradient. -/
theorem OneStepNeumannCellMinimizer.energy_le_of_gradient_quarter
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (X : OneStepNeumannCellMinimizer Q a u.grad)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {ellipticity : ℝ} (hell : 0 ≤ ellipticity)
    (hcenter : cubeAverageVec Q u.grad = 0)
    (hgrad : MemLp X.potential.toH1Function.grad
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q (1 / 4 : ℝ) N
          X.potential.toH1Function.grad ≤
        Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x)))) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          oneStepQuarterCellConst d) ^ 2 * ellipticity *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) (oneStepCellB Q H) := by
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) u.grad
  let B : ℝ := oneStepCellB Q H
  let C : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))
  let D : ℝ := oneStepQuarterCellConst d
  have hA : 0 ≤ A := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u.grad
  have hB : 0 ≤ B := oneStepCellB_nonneg Q H
  have hD : 0 ≤ D := (oneStepQuarterCellConst_pos d).le
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (by norm_num) _)
  have hCD : 0 ≤ C * D := by
    exact mul_nonneg hC hD
  have hu : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
      u.grad_memVectorL2
  have hpairRaw := oneStep_abs_volumeAverage_pairing_le_of_qOne_besov_bounds
    Q X.potential.toH1Function.grad u.grad
      (by norm_num : (0 : ℝ) < 1 / 4) hgrad hu hcenter
      (mul_nonneg hD (oneStepCellBesovSize_nonneg hA hB)) hneg
      (fun i N ↦ by
        simpa only [A, B, D, mul_assoc] using
          oneStep_gradient_qOne_dualTest_quarter_le Q u H i N)
  have hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (u.grad x) (X.potential.toH1Function.grad x))| ≤
        (C * D) * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))) *
          oneStepCellBesovSize A B := by
    dsimp only [C] at hpairRaw ⊢
    calc
      _ ≤ _ := hpairRaw
      _ = _ := by ring
  simpa only [A, B, C, D] using
    X.energy_le_two_mul_cellBesovError hEll hCD hell hA hB hpair

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
