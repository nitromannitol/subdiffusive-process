module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepRandomCellSpecialization
public import Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12Embedding
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
public import Homogenization.Sobolev.W1p.FiniteMeasureDowngrade
public import Homogenization.Book.Ch03.Theorems.SobolevPublic

@[expose] public section

/-!
# Quarter-Besov control for a vector `H¹` field

The Neumann cell fluctuation in the one-step argument is solenoidal rather
than a gradient.  This module records the coordinatewise `H¹` analogue of
the gradient-only interpolation in `OneStepRandomCellSpecialization`.

The proof uses the same two endpoints as the manuscript: the normalized
parent `L²` size at order zero and the cube `W¹,² → B¹_(2,∞)` embedding at
order one.  It is stated on the existing `CubeVectorH1Function` carrier so
the literal field `exp(H) q - grad W` can be inserted without pretending it
is itself a gradient.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The order-zero depth estimate depends only on vector `L²` membership;
no gradient representation of the vector field is needed. -/
theorem oneStep_cubeBesovDepthSeminorm_zero_component_le
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (i : Fin d) (j : ℕ) :
    cubeBesovDepthSeminorm Q 0 (2 : ℝ≥0∞) (fun x ↦ F x i) j ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) F := by
  have hlocal : ∀ R ∈ descendantsAtDepth Q j,
      cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R F) ≤
        2 * cubeLpNorm R (2 : ℝ≥0∞) F := by
    intro R hR
    exact cubeLpNorm_two_cubeFluctuationVec_le_two_mul_cubeLpNorm_two R F
      (memLp_on_descendant_of_memLp_generic hR hF)
  have havg : cubeBesovPositiveVectorDepthAverage Q F j ≤
      4 * descendantsAverage Q j
        (fun R ↦ (cubeLpNorm R (2 : ℝ≥0∞) F) ^ 2) := by
    unfold cubeBesovPositiveVectorDepthAverage
    calc
      descendantsAverage Q j
          (fun R ↦ cubeLpNorm R (2 : ℝ≥0∞)
            (cubeFluctuationVec R F) ^ 2) ≤
          descendantsAverage Q j
            (fun R ↦ (2 * cubeLpNorm R (2 : ℝ≥0∞) F) ^ 2) := by
        refine descendantsAverage_le_descendantsAverage Q j ?_
        intro R hR
        have hleft := cubeLpNorm_nonneg R (2 : ℝ≥0∞)
          (cubeFluctuationVec R F)
        have hright := cubeLpNorm_nonneg R (2 : ℝ≥0∞) F
        nlinarith [hlocal R hR]
      _ = 4 * descendantsAverage Q j
          (fun R ↦ (cubeLpNorm R (2 : ℝ≥0∞) F) ^ 2) := by
        rw [← descendantsAverage_mul_left]
        congr 1
        funext R
        ring
  have hpartition := descendantsAverage_cubeLpNorm_two_sq_eq_cubeLpNorm_two_sq
    Q F j hF
  have hcomponent :=
    cubeBesovDepthAverage_two_component_le_positiveVectorDepthAverage
      Q F i j hF
  have hroot :
      (cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x ↦ F x i) j) ^
          (1 / 2 : ℝ) ≤ 2 * cubeLpNorm Q (2 : ℝ≥0∞) F := by
    have htotal : cubeBesovDepthAverage Q (2 : ℝ≥0∞)
        (fun x ↦ F x i) j ≤
        4 * (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ 2 := by
      calc
        _ ≤ cubeBesovPositiveVectorDepthAverage Q F j := hcomponent
        _ ≤ 4 * descendantsAverage Q j
            (fun R ↦ (cubeLpNorm R (2 : ℝ≥0∞) F) ^ 2) := havg
        _ = 4 * (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ 2 := by
          rw [hpartition]
    have hleft0 := cubeBesovDepthAverage_nonneg Q (2 : ℝ≥0∞)
      (fun x ↦ F x i) j
    have hnorm0 := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F
    rw [← Real.sqrt_eq_rpow]
    have hsqrtSq := Real.sq_sqrt hleft0
    have hsqrt0 := Real.sqrt_nonneg
      (cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x ↦ F x i) j)
    nlinarith
  simpa [cubeBesovDepthSeminorm, cubeBesovDepthWeight] using hroot

/-- Coordinatewise finite `B^(1/4)_(2,∞)` control for an arbitrary vector
`H¹` field.  The fine endpoint is kept as the sum of normalized coordinate
gradient norms; this avoids any gradient-field assumption.  The subsequent
source-cell specialization inserts the cell-side normalization. -/
theorem oneStep_cubeVectorH1_cubeBesovPartialSeminormTop_quarter_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (G : CubeVectorH1Function Q) (i : Fin d) (N : ℕ) :
    cubeBesovPartialSeminormTop Q (1 / 4 : ℝ) (2 : ℝ≥0∞) N
        (fun x ↦ G.toField x i) ≤
      (max 2 (cubeBesovW12EmbeddingConstant d)) *
        oneStepCellBesovSize
          (cubeLpNorm Q (2 : ℝ≥0∞) G.toField)
          (∑ k : Fin d,
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) G.toField
  let B : ℝ := ∑ k : Fin d,
    cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x ↦ euclideanNorm ((G.coord k).grad x))
  let C : ℝ := max 2 (cubeBesovW12EmbeddingConstant d)
  have hA : 0 ≤ A := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) G.toField
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun k _ ↦
      cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
        (fun x ↦ euclideanNorm ((G.coord k).grad x))
  have hC : 0 ≤ C := le_trans (by norm_num) (le_max_left _ _)
  apply oneStep_cubeBesovPartialSeminormTop_quarter_le_of_zero_one_bounds
    Q (fun x ↦ G.toField x i) N hA hB hC
  · intro j
    have hzero := oneStep_cubeBesovDepthSeminorm_zero_component_le
      Q G.toField G.memLp_toField_normalizedCubeMeasure i j
    have htwo : (2 : ℝ) ≤ C := le_max_left _ _
    exact hzero.trans <| mul_le_mul_of_nonneg_right htwo hA
  · intro j
    let u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞) :=
      (G.coord i).toW1pOfExponentLETwo FiniteLpExponent.two (by norm_num)
    have hpartial :=
      cubeBesovPartialSeminormTop_one_two_le_normalizedW1pSeminorm Q j u
    have hdepth : cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
        (fun x ↦ G.toField x i) j ≤
        cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j
          (fun x ↦ G.toField x i) := by
      unfold cubeBesovPartialSeminormTop
      exact Finset.le_sup' (f := fun k ↦
        cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
          (fun x ↦ G.toField x i) k) (by simp)
    have hfine : cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
        (fun x ↦ G.toField x i) j ≤
        cubeBesovW12EmbeddingConstant d *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x)) := by
      calc
        _ ≤ cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j
            (fun x ↦ G.toField x i) := hdepth
        _ = cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j u.toFun := by
          congr 1
        _ ≤ cubeBesovW12EmbeddingConstant d *
            BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
              ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
                (Homogenization.Book.Ch02.openCubeSet_nonempty Q))
              (2 : ℝ≥0∞) (by norm_num) (by norm_num) u := hpartial
        _ = cubeBesovW12EmbeddingConstant d *
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord i).grad x)) := by
          rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad]
          rfl
    have hCi : cubeBesovW12EmbeddingConstant d *
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x ↦ euclideanNorm ((G.coord i).grad x)) ≤
        C * ∑ k : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord k).grad x)) := by
      have hconst : cubeBesovW12EmbeddingConstant d ≤ C := le_max_right _ _
      have hi : cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x ↦ euclideanNorm ((G.coord i).grad x)) ≤
          ∑ k : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord k).grad x)) :=
        Finset.single_le_sum
          (fun k _ ↦ cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord k).grad x)))
          (Finset.mem_univ i)
      exact mul_le_mul hconst hi
        (cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
          (fun x ↦ euclideanNorm ((G.coord i).grad x)))
        hC
    calc
      _ ≤ cubeBesovW12EmbeddingConstant d *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x)) := hfine
      _ ≤ C * ∑ k : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord k).grad x)) := hCi
      _ = C * B := by rfl

/-- Scale-normalized interpolation of order-zero and order-one depth bounds.
The fine endpoint `B` has inverse-length units, so the source-facing cell
observable is `side(Q) * B`. -/
theorem oneStep_cubeBesovPartialSeminormTop_quarter_le_normalized_of_zero_one
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hzero : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q 0 (2 : ℝ≥0∞) u j ≤ C * A)
    (hone : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) u j ≤ C * B) :
    cubeBesovPartialSeminormTop Q (1 / 4 : ℝ) (2 : ℝ≥0∞) N u ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) Q * C *
        oneStepCellBesovSize A (cubeScaleFactor Q * B) := by
  have hscaleB : 0 ≤ cubeScaleFactor Q * B :=
    mul_nonneg (cubeScaleFactor_nonneg Q) hB
  apply oneStep_cubeBesovPartialSeminormTop_quarter_le_normalized
    Q u N hA hscaleB hC
  · intro j
    let rho : ℝ := (3 : ℝ)⁻¹ ^ j
    let D : ℝ :=
      (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ^ (1 / 2 : ℝ)
    have hrho : 0 < rho := by dsimp [rho]; positivity
    have hscaleQ : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    have hs0 : D ≤ C * A := by
      simpa [cubeBesovDepthSeminorm, cubeBesovDepthWeight, rho, D] using hzero j
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
    have hmul := mul_le_mul_of_nonneg_left hs0 hfactor
    convert hmul using 1
    all_goals rw [Real.rpow_neg hscaleQ.le]
    all_goals ring
  · intro j
    let rho : ℝ := (3 : ℝ)⁻¹ ^ j
    let D : ℝ :=
      (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ^ (1 / 2 : ℝ)
    have hrho : 0 < rho := by dsimp [rho]; positivity
    have hscaleQ : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    have honeD : (cubeScaleFactor Q * rho) ^ (-1 : ℝ) * D ≤ C * B := by
      have honej := hone j
      rw [cubeBesovDepthSeminorm, cubeBesovDepthWeight] at honej
      simpa only [show cubeScaleFactor Q / (3 : ℝ) ^ j =
        cubeScaleFactor Q * rho by simp [rho, div_eq_mul_inv], D] using! honej
    let factor : ℝ := cubeScaleFactor Q ^ (3 / 4 : ℝ) * rho ^ (3 / 4 : ℝ)
    have hmul := mul_le_mul_of_nonneg_left honeD
      (by dsimp [factor]; positivity : 0 ≤ factor)
    change (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-(1 / 4 : ℝ)) * D ≤
      (cubeBesovScaleWeight (1 / 4 : ℝ) Q * C) *
        (cubeScaleFactor Q * B) * Real.sqrt (rho * Real.sqrt rho)
    have hrthree : Real.sqrt (rho * Real.sqrt rho) = rho ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [Real.mul_rpow hrho.le (Real.rpow_nonneg hrho.le _),
        ← Real.rpow_mul hrho.le, ← Real.rpow_add hrho]
      norm_num
    rw [show cubeScaleFactor Q / (3 : ℝ) ^ j = cubeScaleFactor Q * rho by
      simp [rho, div_eq_mul_inv], Real.mul_rpow hscaleQ.le hrho.le,
      Real.rpow_neg hscaleQ.le, Real.rpow_neg hrho.le, hrthree]
    unfold cubeBesovScaleWeight
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
    have hrightFactor : factor * (C * B) =
        cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) * C *
          (cubeScaleFactor Q * B) * rho ^ (3 / 4 : ℝ) := by
      dsimp [factor]
      calc
        cubeScaleFactor Q ^ (3 / 4 : ℝ) * rho ^ (3 / 4 : ℝ) * (C * B) =
            (cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) * cubeScaleFactor Q) *
              C * B * rho ^ (3 / 4 : ℝ) := by
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

/-- Source-normalized quarter-Besov estimate for every coordinate of an
arbitrary vector `H¹` field. -/
theorem oneStep_cubeVectorH1_cubeBesovPartialSeminormTop_quarter_le_normalized
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (G : CubeVectorH1Function Q) (i : Fin d) (N : ℕ) :
    cubeBesovPartialSeminormTop Q (1 / 4 : ℝ) (2 : ℝ≥0∞) N
        (fun x ↦ G.toField x i) ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) Q *
        (max 2 (cubeBesovW12EmbeddingConstant d)) *
        oneStepCellBesovSize
          (cubeLpNorm Q (2 : ℝ≥0∞) G.toField)
          (cubeScaleFactor Q * ∑ k : Fin d,
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) G.toField
  let B : ℝ := ∑ k : Fin d,
    cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x ↦ euclideanNorm ((G.coord k).grad x))
  let C : ℝ := max 2 (cubeBesovW12EmbeddingConstant d)
  have hA : 0 ≤ A := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) G.toField
  have hB : 0 ≤ B := Finset.sum_nonneg fun k _ ↦
    cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
      (fun x ↦ euclideanNorm ((G.coord k).grad x))
  have hC : 0 ≤ C := le_trans (by norm_num) (le_max_left _ _)
  apply oneStep_cubeBesovPartialSeminormTop_quarter_le_normalized_of_zero_one
    Q (fun x ↦ G.toField x i) N hA hB hC
  · intro j
    have hzero := oneStep_cubeBesovDepthSeminorm_zero_component_le
      Q G.toField G.memLp_toField_normalizedCubeMeasure i j
    exact hzero.trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) hA
  · intro j
    let u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞) :=
      (G.coord i).toW1pOfExponentLETwo FiniteLpExponent.two (by norm_num)
    have hpartial :=
      cubeBesovPartialSeminormTop_one_two_le_normalizedW1pSeminorm Q j u
    have hdepth : cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
        (fun x ↦ G.toField x i) j ≤
        cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j
          (fun x ↦ G.toField x i) := by
      unfold cubeBesovPartialSeminormTop
      exact Finset.le_sup' (f := fun k ↦
        cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
          (fun x ↦ G.toField x i) k) (by simp)
    have hfine : cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
        (fun x ↦ G.toField x i) j ≤
        cubeBesovW12EmbeddingConstant d *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x)) := by
      calc
        _ ≤ _ := hdepth
        _ = cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j u.toFun := by
          congr 1
        _ ≤ _ := hpartial
        _ = cubeBesovW12EmbeddingConstant d *
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord i).grad x)) := by
          rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad]
          rfl
    calc
      _ ≤ cubeBesovW12EmbeddingConstant d *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x)) := hfine
      _ ≤ C * B := by
        have hconst : cubeBesovW12EmbeddingConstant d ≤ C := le_max_right _ _
        have hi : cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x)) ≤ B := by
          dsimp [B]
          exact Finset.single_le_sum
            (fun k _ ↦ cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x)))
            (Finset.mem_univ i)
        exact mul_le_mul hconst hi
          (cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x))) hC

/-- Exact `q = 1` dual-test interface for a centered vector `H¹` datum.
This is the solenoidal counterpart of
`oneStep_gradient_qOne_dualTest_quarter_le`. -/
theorem oneStep_cubeVectorH1_qOne_dualTest_quarter_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (G : CubeVectorH1Function Q) (i : Fin d) (N : ℕ) :
    cubeBesovDualTestNorm Q (1 / 4 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x ↦ cubeFluctuationVec Q G.toField x i) ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) Q *
        ((max 2 (cubeBesovW12EmbeddingConstant d)) *
          oneStepCellBesovSize
            (cubeLpNorm Q (2 : ℝ≥0∞) G.toField)
            (cubeScaleFactor Q * ∑ k : Fin d,
              cubeLpNorm Q (2 : ℝ≥0∞)
                (fun x ↦ euclideanNorm ((G.coord k).grad x)))) := by
  have hG : MemLp G.toField (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    G.memLp_toField_normalizedCubeMeasure
  apply oneStep_qOne_dualTest_of_positiveTop_component_bounds Q G.toField
  intro k K
  have hmain :=
    oneStep_cubeVectorH1_cubeBesovPartialSeminormTop_quarter_le_normalized
      Q G k K
  rw [← cubeFluctuation_component_eq_cubeFluctuationVec_component Q G.toField k,
    oneStep_cubeBesovPartialSeminormTop_cubeFluctuation_eq Q
      (1 / 4 : ℝ) (fun x ↦ G.toField x k) K
      (memLp_component_of_memLp G.toField k hG)]
  simpa only [mul_assoc] using hmain

/-- Centered form of the vector `H¹` interpolation.  Unlike the preceding
raw-field estimate, its order-zero observable is exactly the manuscript's
cell fluctuation `A_z`; subtracting the cell average leaves the order-one
endpoint unchanged. -/
theorem oneStep_cubeVectorH1_cubeFluctuationPartialSeminormTop_quarter_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (G : CubeVectorH1Function Q) (i : Fin d) (N : ℕ) :
    cubeBesovPartialSeminormTop Q (1 / 4 : ℝ) (2 : ℝ≥0∞) N
        (fun x ↦ cubeFluctuationVec Q G.toField x i) ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) Q *
        (max 2 (cubeBesovW12EmbeddingConstant d)) *
        oneStepCellBesovSize
          (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q G.toField))
          (cubeScaleFactor Q * ∑ k : Fin d,
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let F : Vec d → Vec d := cubeFluctuationVec Q G.toField
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let B : ℝ := ∑ k : Fin d,
    cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x ↦ euclideanNorm ((G.coord k).grad x))
  let C : ℝ := max 2 (cubeBesovW12EmbeddingConstant d)
  have hG : MemLp G.toField (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    G.memLp_toField_normalizedCubeMeasure
  have hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q G.toField hG
  have hA : 0 ≤ A := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F
  have hB : 0 ≤ B := Finset.sum_nonneg fun k _ ↦
    cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
      (fun x ↦ euclideanNorm ((G.coord k).grad x))
  have hC : 0 ≤ C := le_trans (by norm_num) (le_max_left _ _)
  apply oneStep_cubeBesovPartialSeminormTop_quarter_le_normalized_of_zero_one
    Q (fun x ↦ F x i) N hA hB hC
  · intro j
    have hzero := oneStep_cubeBesovDepthSeminorm_zero_component_le Q F hF i j
    exact hzero.trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) hA
  · intro j
    let u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞) :=
      (G.coord i).toW1pOfExponentLETwo FiniteLpExponent.two (by norm_num)
    have hpartial :=
      cubeBesovPartialSeminormTop_one_two_le_normalizedW1pSeminorm Q j u
    have hdepth : cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
        (fun x ↦ F x i) j ≤
        cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j
          (fun x ↦ F x i) := by
      unfold cubeBesovPartialSeminormTop
      exact Finset.le_sup' (f := fun k ↦
        cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x ↦ F x i) k)
        (by simp)
    have hcenteredPartial :
        cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j
            (fun x ↦ F x i) =
          cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j
            (fun x ↦ G.toField x i) := by
      rw [show (fun x ↦ F x i) =
          cubeFluctuation Q (fun x ↦ G.toField x i) by
        exact (cubeFluctuation_component_eq_cubeFluctuationVec_component
          Q G.toField i).symm]
      exact oneStep_cubeBesovPartialSeminormTop_cubeFluctuation_eq
        Q 1 (fun x ↦ G.toField x i) j
          (memLp_component_of_memLp G.toField i hG)
    have hfine : cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
        (fun x ↦ F x i) j ≤
        cubeBesovW12EmbeddingConstant d *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x)) := by
      calc
        _ ≤ _ := hdepth
        _ = cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j
            (fun x ↦ G.toField x i) := hcenteredPartial
        _ = cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) j u.toFun := by
          congr 1
        _ ≤ _ := hpartial
        _ = cubeBesovW12EmbeddingConstant d *
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord i).grad x)) := by
          rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad]
          rfl
    calc
      _ ≤ cubeBesovW12EmbeddingConstant d *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x)) := hfine
      _ ≤ C * B := by
        have hconst : cubeBesovW12EmbeddingConstant d ≤ C := le_max_right _ _
        have hi : cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x)) ≤ B := by
          dsimp [B]
          exact Finset.single_le_sum
            (fun k _ ↦ cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x)))
            (Finset.mem_univ i)
        exact mul_le_mul hconst hi
          (cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord i).grad x))) hC

/-- Exact centered dual-test bound with the manuscript's `A_z` observable. -/
theorem oneStep_cubeVectorH1_cubeFluctuation_qOne_dualTest_quarter_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (G : CubeVectorH1Function Q) (i : Fin d) (N : ℕ) :
    cubeBesovDualTestNorm Q (1 / 4 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x ↦ cubeFluctuationVec Q G.toField x i) ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) Q *
        ((max 2 (cubeBesovW12EmbeddingConstant d)) *
          oneStepCellBesovSize
            (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q G.toField))
            (cubeScaleFactor Q * ∑ k : Fin d,
              cubeLpNorm Q (2 : ℝ≥0∞)
                (fun x ↦ euclideanNorm ((G.coord k).grad x)))) := by
  apply oneStep_qOne_dualTest_of_positiveTop_component_bounds Q G.toField
  intro k K
  simpa only [mul_assoc] using
    oneStep_cubeVectorH1_cubeFluctuationPartialSeminormTop_quarter_le Q G k K

/-- Dual cell-energy estimate for the centered datum carried by an arbitrary
vector `H¹` field.  This is the solenoidal counterpart of
`OneStepNeumannCellMinimizer.energy_le_of_gradient_quarter`: the order-zero
observable is the centered vector norm and the order-one observable is the
sum of the coordinate-gradient norms. -/
theorem OneStepNeumannCellMinimizer.energy_le_of_vectorH1_quarter
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {lam Lam : ℝ} {F : Vec d → Vec d} (G : CubeVectorH1Function Q)
    (X : OneStepNeumannCellMinimizer Q a F)
    (hF_eq : F = cubeFluctuationVec Q G.toField)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {ellipticity : ℝ} (hell : 0 ≤ ellipticity)
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
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 * ellipticity *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) F)
          (cubeScaleFactor Q * ∑ k : Fin d,
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let B : ℝ := cubeScaleFactor Q * ∑ k : Fin d,
    cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x ↦ euclideanNorm ((G.coord k).grad x))
  let C : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))
  let D : ℝ := max 2 (cubeBesovW12EmbeddingConstant d)
  have hA : 0 ≤ A := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F
  have hB : 0 ≤ B := mul_nonneg (cubeScaleFactor_nonneg Q) <|
    Finset.sum_nonneg fun k _ ↦ cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
      (fun x ↦ euclideanNorm ((G.coord k).grad x))
  have hD : 0 ≤ D := le_trans (by norm_num) (le_max_left _ _)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (by norm_num) _)
  have hCD : 0 ≤ C * D := mul_nonneg hC hD
  have hrawCube : MemVectorL2 (cubeSet Q) G.toField := by
    simpa only [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using
        G.memVectorL2_toField_openCubeSet
  have hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hF_eq ▸ memLp_cubeFluctuationVec Q G.toField
      G.memLp_toField_normalizedCubeMeasure
  have hcenter : cubeAverageVec Q F = 0 := by
    rw [hF_eq]
    simpa only [cubeFluctuationVec] using!
      cubeAverageVec_centered_eq_zero Q G.toField hrawCube
  have hFF : cubeFluctuationVec Q F = F := by
    funext x i
    simp only [cubeFluctuationVec_apply, hcenter, sub_zero]
  have hpairRaw := oneStep_abs_volumeAverage_pairing_le_of_qOne_besov_bounds
    Q X.potential.toH1Function.grad F
      (by norm_num : (0 : ℝ) < 1 / 4) hgrad hF hcenter
      (mul_nonneg hD (oneStepCellBesovSize_nonneg hA hB)) hneg
      (fun i N ↦ by
        rw [hFF]
        rw [hF_eq]
        simpa only [A, B, D, hF_eq, mul_assoc] using
          oneStep_cubeVectorH1_cubeFluctuation_qOne_dualTest_quarter_le Q G i N)
  have hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (F x) (X.potential.toH1Function.grad x))| ≤
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

/-- Almost-everywhere datum transport for the vector-`H¹` energy estimate.
The selected Neumann potential and its physical flux are unchanged by
`congrDatum`; only the representative of the prescribed datum changes. -/
theorem OneStepNeumannCellMinimizer.energy_le_of_vectorH1_quarter_ae
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {lam Lam : ℝ} {F : Vec d → Vec d} (G : CubeVectorH1Function Q)
    (X : OneStepNeumannCellMinimizer Q a F)
    (hF_ae : F =ᵐ[volumeMeasureOn (openCubeSet Q)]
      cubeFluctuationVec Q G.toField)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {ellipticity : ℝ} (hell : 0 ≤ ellipticity)
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
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 * ellipticity *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q G.toField))
          (cubeScaleFactor Q * ∑ k : Fin d,
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  let Y : OneStepNeumannCellMinimizer Q a
      (cubeFluctuationVec Q G.toField) := X.congrDatum hF_ae
  have hYgrad : MemLp Y.potential.toH1Function.grad
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hgrad
  have hYneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q (1 / 4 : ℝ) N
          Y.potential.toH1Function.grad ≤
        Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (Y.potential.toH1Function.grad x) (Y.flux x))) := by
    exact hneg
  exact Y.energy_le_of_vectorH1_quarter G rfl hEll hell hYgrad hYneg

/-- The Euclidean magnitude of a finite-dimensional vector field costs only
the explicit dimension factor relative to the project's native supremum-norm
`L²` carrier.  This is the norm-conversion step needed for the vector-`H¹`
Neumann datum. -/
theorem cubeLpNorm_euclideanNorm_le_dimension_mul
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ euclideanNorm (F x)) ≤
      (d : ℝ) * cubeLpNorm Q (2 : ℝ≥0∞) F := by
  unfold cubeLpNorm
  have hscaled : MemLp (fun x ↦ (d : ℝ) * ‖F x‖)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hF.norm.const_mul (d : ℝ)
  have hmono : eLpNorm (fun x ↦ euclideanNorm (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) ≤
    eLpNorm (fun x ↦ (d : ℝ) * ‖F x‖) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    have hcont : Continuous (euclideanNorm : Vec d → ℝ) := by
      unfold euclideanNorm vecNormSq vecDot
      fun_prop
    apply eLpNorm_mono_ae (hcont.comp_aestronglyMeasurable hF.aestronglyMeasurable)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg d) (norm_nonneg _))] using
        euclideanNorm_le_dimension_mul_norm (F x)
  calc
    (eLpNorm (fun x ↦ euclideanNorm (F x)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q)).toReal ≤
      (eLpNorm (fun x ↦ (d : ℝ) * ‖F x‖) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q)).toReal :=
      ENNReal.toReal_mono hscaled.eLpNorm_ne_top hmono
    _ = (d : ℝ) *
        (eLpNorm F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)).toReal := by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have hfun : (fun x ↦ (d : ℝ) * ‖F x‖) =
          (d : ℝ) • fun x ↦ ‖F x‖ := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
      rw [hfun, eLpNorm_const_smul, ENNReal.toReal_mul, eLpNorm_norm _ hF.aestronglyMeasurable]
      rw [← ofReal_norm_eq_enorm,
        ENNReal.toReal_ofReal (norm_nonneg (d : ℝ))]
      simp only [Real.norm_eq_abs, abs_of_nonneg hd0]

/-- Coordinatewise weak derivatives dominate the Euclidean-gradient size of
a vector `H¹` carrier with an explicit dimension factor. -/
theorem cubeVectorH1_euclideanGradientSum_le
    {d : ℕ} (Q : TriadicCube d) (G : CubeVectorH1Function Q) :
    ∑ k : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x ↦ euclideanNorm ((G.coord k).grad x)) ≤
      (d : ℝ) * ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
        ∑ k : Fin d, (G.coord k).gradientCoordL2NormSum := by
  calc
    ∑ k : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x ↦ euclideanNorm ((G.coord k).grad x)) ≤
      ∑ k : Fin d, (d : ℝ) *
        cubeLpNorm Q (2 : ℝ≥0∞) (G.coord k).grad := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          exact cubeLpNorm_euclideanNorm_le_dimension_mul Q
            (G.coord k).grad (by
              apply MemLp.of_eval
              intro i
              exact (G.coord k).grad_memL2_normalizedCubeMeasure i)
    _ ≤ ∑ k : Fin d, (d : ℝ) *
        (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
          (G.coord k).gradientCoordL2NormSum) := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          exact mul_le_mul_of_nonneg_left
            (cubeLpNorm_two_grad_le_volume_inv_rpow_half_mul_gradientCoordL2NormSum
              (G.coord k)) (Nat.cast_nonneg d)
    _ = (d : ℝ) * ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
        ∑ k : Fin d, (G.coord k).gradientCoordL2NormSum := by
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- Coordinatewise mean-zero Poincare on a cell for a vector `H¹` carrier.
The right side is the derivative-size slot used by the dual cell Besov
majorant. -/
theorem cubeLpNorm_two_cubeFluctuationVec_toField_le_gradientSize
    {d : ℕ} [NeZero d] (R : TriadicCube d) (G : CubeVectorH1Function R) :
    cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R G.toField) ≤
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        (cubeScaleFactor R * ∑ k : Fin d,
          cubeLpNorm R (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  have hG : MemLp G.toField (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    G.memLp_toField_normalizedCubeMeasure
  have hfluct : MemLp (cubeFluctuationVec R G.toField) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R) :=
    memLp_cubeFluctuationVec R G.toField hG
  have hvec := Homogenization.Book.Ch03.cubeLpNorm_two_vec_le_sum_components R
    (cubeFluctuationVec R G.toField) hfluct
  have hcoord : ∀ k : Fin d,
      cubeLpNorm R (2 : ℝ≥0∞)
          (fun x ↦ cubeFluctuationVec R G.toField x k) ≤
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
          cubeScaleFactor R *
            cubeLpNorm R (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x)) := by
    intro k
    let u : W1pFunction (openCubeSet R) (2 : ℝ≥0∞) := {
      toFun := (G.coord k).toFun
      grad := (G.coord k).grad
      memLp := (G.coord k).memL2
      gradMemLp := (G.coord k).gradMemL2
      hasWeakGradient := (G.coord k).hasWeakGradient
    }
    have hp := cubeBesovOscillation_two_le_cubeScaleFactor_mul_normalizedW1pSeminorm
      R u
    rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad]
      at hp
    simpa only [cubeBesovW12LocalPoincareConstant, u,
      cubeFluctuationVec_apply] using! hp
  calc
    cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R G.toField) ≤
        ∑ k : Fin d, cubeLpNorm R (2 : ℝ≥0∞)
          (fun x ↦ cubeFluctuationVec R G.toField x k) := hvec
    _ ≤ ∑ k : Fin d,
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
          cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞)
            (fun x ↦ euclideanNorm ((G.coord k).grad x)) := by
      exact Finset.sum_le_sum fun k _ ↦ hcoord k
    _ = _ := by
      rw [← Finset.mul_sum, ← mul_assoc]


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
