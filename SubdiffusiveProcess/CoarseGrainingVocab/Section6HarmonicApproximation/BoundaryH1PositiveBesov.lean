module

public import Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12Embedding
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms.Bounds
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.VectorProduct

@[expose] public section

/-!
# Positive Besov control of a boundary `H¹` datum

The public cube Sobolev layer gives the scale-free embedding
`W^{1,2} -> B¹_{2,∞}`.  The boundary cutoff pairing needs instead the
summable `Bˢ_{2,2}` seminorm, with `s < 1`.  This file supplies the
geometric scale summation and packages the result for an `H1Function`.

This is the positive-norm leg in the decomposition of

the actual normalized descendant Poincare/partition input is reused from
CoarseGraining's `CubeBesovPoincare/W12Embedding.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
theorem positiveScalarDepthSeminorm_eq_geometric_mul_one
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ) :
    cubeBesovPositiveScalarDepthSeminorm Q s v j =
      Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) *
        cubeBesovPositiveScalarDepthSeminorm Q 1 v j := by
  unfold cubeBesovPositiveScalarDepthSeminorm
  rw [← mul_assoc]
  congr 1
  calc
    Real.rpow (3 : ℝ) (s * (j : ℝ)) =
        Real.rpow (3 : ℝ) (((s - 1) * (j : ℝ)) + 1 * (j : ℝ)) := by
          congr 1
          ring
    _ = Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) *
        Real.rpow (3 : ℝ) (1 * (j : ℝ)) :=
      Real.rpow_add (by norm_num) _ _

omit [NeZero d] in
theorem positiveScalarDepthSeminorm_one_eq_scale_mul_depthSeminorm
    (Q : TriadicCube d) (v : Vec d → ℝ) (j : ℕ) :
    cubeBesovPositiveScalarDepthSeminorm Q 1 v j =
      cubeScaleFactor Q * cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) v j := by
  rw [cubeBesovPositiveScalarDepthSeminorm_eq_scaleWeight_neg_mul_cubeBesovDepthSeminorm_two]
  congr 1
  simp [cubeBesovScaleWeight]

omit [NeZero d] in
/-- The finite `Bˢ_{2,2}` scalar seminorm is controlled by the finite
`B¹_{2,∞}` seminorm.  The constant is uniform in the terminal depth. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_le_partialTop_one
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ) (hs : s < 1) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s N v ≤
      cubeScaleFactor Q *
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N v := by
  let r : ℝ := Real.rpow (3 : ℝ) (2 * (s - 1))
  let A : ℝ := cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N v
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hA : 0 ≤ A := cubeBesovPartialSeminormTop_nonneg Q 1 (2 : ℝ≥0∞) N v
  have hdepth : ∀ j ∈ Finset.range (N + 1),
      cubeBesovPositiveScalarDepthSeminorm Q s v j ≤
        cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) * A := by
    intro j hj
    rw [positiveScalarDepthSeminorm_eq_geometric_mul_one,
      positiveScalarDepthSeminorm_one_eq_scale_mul_depthSeminorm]
    have hjA : cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) v j ≤ A := by
      dsimp [A]
      unfold cubeBesovPartialSeminormTop
      exact Finset.le_sup' (s := Finset.range (N + 1))
        (f := fun k => cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) v k) hj
    have hcoeff : 0 ≤ Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hscale : 0 ≤ cubeScaleFactor Q := cubeScaleFactor_nonneg Q
    calc
      Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) *
          (cubeScaleFactor Q * cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) v j)
          = cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) *
              cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) v j := by ring
      _ ≤ cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) * A :=
        mul_le_mul_of_nonneg_left hjA (mul_nonneg hscale hcoeff)
  have hsqGeom :
      ∑ j ∈ Finset.range (N + 1),
          (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2 ≤
        (cubeScaleFactor Q * A) ^ 2 *
          ∑ j ∈ Finset.range (N + 1), r ^ j := by
    calc
      ∑ j ∈ Finset.range (N + 1),
          (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2
          ≤ ∑ j ∈ Finset.range (N + 1),
              (cubeScaleFactor Q *
                Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) * A) ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact pow_le_pow_left₀
              (cubeBesovPositiveScalarDepthSeminorm_nonneg Q s v j)
              (hdepth j hj) 2
      _ = (cubeScaleFactor Q * A) ^ 2 *
          ∑ j ∈ Finset.range (N + 1), r ^ j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            have hpow :
                (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 = r ^ j := by
              dsimp [r]
              calc
                (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 =
                    Real.rpow (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) (2 : ℝ) := by
                      exact (Real.rpow_natCast
                        (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) 2).symm
                _ = Real.rpow (3 : ℝ) (((s - 1) * (j : ℝ)) * 2) := by
                      exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
                        ((s - 1) * (j : ℝ)) 2).symm
                _ = Real.rpow (3 : ℝ) ((2 * (s - 1)) * (j : ℝ)) := by
                      congr 1
                      ring
                _ = Real.rpow (Real.rpow (3 : ℝ) (2 * (s - 1))) (j : ℝ) := by
                      exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
                        (2 * (s - 1)) (j : ℝ)
                _ = (Real.rpow (3 : ℝ) (2 * (s - 1))) ^ j := by
                      exact Real.rpow_natCast
                        (Real.rpow (3 : ℝ) (2 * (s - 1))) j
            calc
              (cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) * A) ^ 2
                  = (cubeScaleFactor Q * A) ^ 2 *
                      (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 := by ring
              _ = (cubeScaleFactor Q * A) ^ 2 * r ^ j := by rw [hpow]
  have hsq :
      ∑ j ∈ Finset.range (N + 1),
          (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2 ≤
        (cubeScaleFactor Q * A) ^ 2 * (1 - r)⁻¹ :=
    hsqGeom.trans (mul_le_mul_of_nonneg_left
      (geom_sum_range_le_of_lt_one hr0 hr1) (sq_nonneg _))
  have hinv0 : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hr1.le)
  have hscaleA : 0 ≤ cubeScaleFactor Q * A :=
    mul_nonneg (cubeScaleFactor_nonneg Q) hA
  calc
    cubeBesovPositiveScalarPartialSeminormTwo Q s N v
        = Real.sqrt (∑ j ∈ Finset.range (N + 1),
            (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2) := rfl
    _ ≤ Real.sqrt ((cubeScaleFactor Q * A) ^ 2 * (1 - r)⁻¹) :=
      Real.sqrt_le_sqrt hsq
    _ = (cubeScaleFactor Q * A) * Real.sqrt ((1 - r)⁻¹) := by
      rw [Real.sqrt_mul (sq_nonneg _)]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hscaleA]
    _ = cubeScaleFactor Q * Real.sqrt ((1 - r)⁻¹) * A := by ring
    _ = cubeScaleFactor Q *
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N v := by
      rfl

omit [NeZero d] in
/-- A single positive-Besov depth is bounded by the ambient normalized
`L²` norm.  This is the low-depth half of the finite-height split. -/
theorem cubeBesovPositiveScalarDepthSeminorm_le_l2
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovPositiveScalarDepthSeminorm Q s v j ≤
      2 * Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        cubeLpNorm Q (2 : ℝ≥0∞) v := by
  have hoscBase : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) v ≤
        2 * cubeLpNorm R (2 : ℝ≥0∞) v := by
    intro R hR
    have hvR := memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR hv
    unfold cubeBesovOscillation cubeFluctuation
    have hconst : MeasureTheory.MemLp (fun _ : Vec d => -cubeAverage R v)
        (2 : ℝ≥0∞) (normalizedCubeMeasure R) := MeasureTheory.memLp_const _
    have hadd : cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => v x - cubeAverage R v) ≤
        cubeLpNorm R (2 : ℝ≥0∞) v +
          cubeLpNorm R (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverage R v) := by
      have hfun : (fun x => v x - cubeAverage R v) =
          fun x => v x + (fun _ : Vec d => -cubeAverage R v) x := by
        funext x
        simp [sub_eq_add_neg]
      rw [hfun]
      exact cubeLpNorm_add_le R (2 : ℝ≥0∞) v
        (fun _ : Vec d => -cubeAverage R v) hvR hconst (by norm_num)
    calc
      cubeLpNorm R (2 : ℝ≥0∞) (fun x => v x - cubeAverage R v)
          ≤ cubeLpNorm R (2 : ℝ≥0∞) v +
              cubeLpNorm R (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverage R v) := hadd
      _ = cubeLpNorm R (2 : ℝ≥0∞) v + ‖cubeAverage R v‖ := by
        rw [cubeLpNorm_const (Q := R) (p := (2 : ℝ≥0∞))
          (c := -cubeAverage R v) (by norm_num)]
        simp
      _ ≤ cubeLpNorm R (2 : ℝ≥0∞) v + cubeLpNorm R (2 : ℝ≥0∞) v := by
        gcongr
        exact norm_cubeAverage_le_cubeLpNorm_two R v hvR
      _ = 2 * cubeLpNorm R (2 : ℝ≥0∞) v := by ring
  have hosc : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) v ≤
        2 * cubeLpNorm R (2 : ℝ≥0∞) v := by
    intro R hR
    exact hoscBase R hR
  have havg : cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j ≤
      4 * cubeL2ScalarDepthAverage Q v j := by
    unfold cubeBesovDepthAverage
    calc
      descendantsAverage Q j
          (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) v) ^ (2 : ℝ))
          ≤ descendantsAverage Q j
              (fun R => (2 * cubeLpNorm R (2 : ℝ≥0∞) v) ^ (2 : ℕ)) := by
            apply descendantsAverage_le_descendantsAverage
            intro R hR
            have hnonneg := cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) v
            have hright : 0 ≤ 2 * cubeLpNorm R (2 : ℝ≥0∞) v :=
              mul_nonneg (by norm_num) (cubeLpNorm_nonneg R (2 : ℝ≥0∞) v)
            simpa [Real.rpow_natCast] using
              pow_le_pow_left₀ hnonneg (hosc R hR) 2
      _ = 4 * cubeL2ScalarDepthAverage Q v j := by
            rw [show (fun R => (2 * cubeLpNorm R (2 : ℝ≥0∞) v) ^ (2 : ℕ)) =
                fun R => 4 * (cubeLpNorm R (2 : ℝ≥0∞) v) ^ (2 : ℕ) by
              funext R
              ring]
            rw [descendantsAverage_mul_left]
            rfl
  have havg' : cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j ≤
      4 * (cubeLpNorm Q (2 : ℝ≥0∞) v) ^ 2 := by
    rw [cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q v j hv] at havg
    exact havg
  have hsqrt : Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j) ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) v := by
    calc
      Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j)
          ≤ Real.sqrt (4 * (cubeLpNorm Q (2 : ℝ≥0∞) v) ^ 2) :=
        Real.sqrt_le_sqrt havg'
      _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) v := by
        rw [show 4 * (cubeLpNorm Q (2 : ℝ≥0∞) v) ^ 2 =
            (2 * cubeLpNorm Q (2 : ℝ≥0∞) v) ^ 2 by ring]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
        exact mul_nonneg (by norm_num) (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v)
  have havgEq : cubeBesovPositiveScalarDepthAverage Q v j =
      cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j := by
    simp [cubeBesovPositiveScalarDepthAverage, cubeBesovDepthAverage]
  unfold cubeBesovPositiveScalarDepthSeminorm
  rw [havgEq]
  calc
    Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) v j)
        ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            (2 * cubeLpNorm Q (2 : ℝ≥0∞) v) :=
      mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg (by norm_num) _)
    _ = 2 * Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          cubeLpNorm Q (2 : ℝ≥0∞) v := by ring

def boundaryH1ToW12 {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞) where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memL2
  gradMemLp := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

/-- Uniform finite-depth positive `Bˢ_{2,2}` control of an `H¹` scalar by
its normalized gradient norm. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_h1_le
    (Q : TriadicCube d) (s : ℝ) (N : ℕ)
    (u : H1Function (openCubeSet Q)) (hs : s < 1) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s N u.toFun ≤
      cubeScaleFactor Q *
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (cubeBesovW12EmbeddingConstant d *
            cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))) := by
  have hgeom := cubeBesovPositiveScalarPartialSeminormTwo_le_partialTop_one
    Q s N u.toFun hs
  have hW := cubeBesovPartialSeminormTop_one_two_le_normalizedW1pSeminorm
    Q N (boundaryH1ToW12 u)
  rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad] at hW
  exact hgeom.trans (mul_le_mul_of_nonneg_left hW
    (mul_nonneg (cubeScaleFactor_nonneg Q) (Real.sqrt_nonneg _)))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
