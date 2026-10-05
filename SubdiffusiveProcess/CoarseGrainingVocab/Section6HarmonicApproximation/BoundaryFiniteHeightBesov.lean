module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryH1PositiveBesov
public import Homogenization.Sobolev.Foundations.MeanZero

@[expose] public section

/-!
# A finite-height positive-Besov split for rough boundary data

The nonzero boundary datum is not harmonic, so the Chapter-3 harmonic
explicit-height wrapper cannot be applied to it.  This file isolates the
underlying interpolation step: below a chosen height use the ambient `L²`
norm, and above it use the `B¹_{2,∞}` control supplied by the weak gradient.

 this is the low/high-depth split inside CoarseGraining's
`CoarseCaccioppoli/Boundary/ExplicitHeight.lean`, adapted to the arbitrary
`H1Function` datum carrier required by the GMC boundary cell.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The `L²` coefficient of the depths strictly below `height`. -/
noncomputable def boundaryFiniteHeightHeadCoeff
    (s : ℝ) (N height : ℕ) : ℝ :=
  Real.sqrt <| ∑ j ∈ Finset.range (N + 1),
    (if j < height then 2 * Real.rpow (3 : ℝ) (s * (j : ℝ)) else 0) ^ 2

/-- The terminal-depth-independent coarse coefficient. -/
noncomputable def boundaryFiniteHeightHeadGlobalCoeff
    (s : ℝ) (height : ℕ) : ℝ :=
  Real.sqrt <| ∑ j ∈ Finset.range height,
    (2 * Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2

/-- The `B¹_{2,∞}` coefficient of the depths at or above `height`. -/
noncomputable def boundaryFiniteHeightTailCoeff
    (Q : TriadicCube d) (s : ℝ) (N height : ℕ) : ℝ :=
  Real.sqrt <| ∑ j ∈ Finset.range (N + 1),
    (if height ≤ j then
      cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))
    else 0) ^ 2

theorem boundaryFiniteHeightHeadCoeff_nonneg (s : ℝ) (N height : ℕ) :
    0 ≤ boundaryFiniteHeightHeadCoeff s N height :=
  Real.sqrt_nonneg _

theorem boundaryFiniteHeightHeadGlobalCoeff_nonneg (s : ℝ) (height : ℕ) :
    0 ≤ boundaryFiniteHeightHeadGlobalCoeff s height :=
  Real.sqrt_nonneg _

theorem boundaryFiniteHeightHeadCoeff_le_global (s : ℝ) (N height : ℕ) :
    boundaryFiniteHeightHeadCoeff s N height ≤
      boundaryFiniteHeightHeadGlobalCoeff s height := by
  have hsumEq :
      ∑ j ∈ Finset.range (N + 1),
          (if j < height then 2 * Real.rpow (3 : ℝ) (s * (j : ℝ)) else 0) ^ 2 =
        ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < height),
          (2 * Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 := by
    simp [Finset.sum_filter]
  have hsubset : (Finset.range (N + 1)).filter (fun j => j < height) ⊆
      Finset.range height := by
    intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  have hsum :
      ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < height),
          (2 * Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 ≤
        ∑ j ∈ Finset.range height,
          (2 * Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j hj hj' => sq_nonneg _)
  unfold boundaryFiniteHeightHeadCoeff boundaryFiniteHeightHeadGlobalCoeff
  rw [hsumEq]
  exact Real.sqrt_le_sqrt hsum

omit [NeZero d] in
theorem boundaryFiniteHeightTailCoeff_nonneg
    (Q : TriadicCube d) (s : ℝ) (N height : ℕ) :
    0 ≤ boundaryFiniteHeightTailCoeff Q s N height :=
  Real.sqrt_nonneg _

omit [NeZero d] in
theorem boundaryFiniteHeightTailWeight_sq
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    (cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 =
      (cubeScaleFactor Q) ^ 2 *
        (Real.rpow (3 : ℝ) (2 * (s - 1))) ^ j := by
  have hpow : (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 =
      (Real.rpow (3 : ℝ) (2 * (s - 1))) ^ j := by
    calc
      (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 =
          Real.rpow (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) (2 : ℝ) := by
        exact (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (3 : ℝ) (((s - 1) * (j : ℝ)) * 2) := by
        exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
          ((s - 1) * (j : ℝ)) 2).symm
      _ = Real.rpow (3 : ℝ) ((2 * (s - 1)) * (j : ℝ)) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow (3 : ℝ) (2 * (s - 1))) (j : ℝ) := by
        exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
          (2 * (s - 1)) (j : ℝ)
      _ = (Real.rpow (3 : ℝ) (2 * (s - 1))) ^ j :=
        Real.rpow_natCast _ j
  rw [mul_pow, hpow]

omit [NeZero d] in
/-- The fine-depth coefficient decays geometrically with the chosen height.
This is the tunable coefficient used for half absorption. -/
theorem boundaryFiniteHeightTailCoeff_le_geometric
    (Q : TriadicCube d) (s : ℝ) (N height : ℕ) (hs : s < 1) :
    boundaryFiniteHeightTailCoeff Q s N height ≤
      cubeScaleFactor Q *
        Real.sqrt ((Real.rpow (3 : ℝ) (2 * (s - 1))) ^ height /
          (1 - Real.rpow (3 : ℝ) (2 * (s - 1)))) := by
  let r : ℝ := Real.rpow (3 : ℝ) (2 * (s - 1))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsumEq :
      ∑ j ∈ Finset.range (N + 1),
          (if height ≤ j then
            cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))
          else 0) ^ 2 =
        (cubeScaleFactor Q) ^ 2 *
          ∑ j ∈ Finset.Ico height (N + 1), r ^ j := by
    calc
      ∑ j ∈ Finset.range (N + 1),
          (if height ≤ j then
            cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))
          else 0) ^ 2 =
          ∑ j ∈ (Finset.range (N + 1)).filter (fun j => height ≤ j),
            (cubeScaleFactor Q *
              Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 := by
        simp [Finset.sum_filter]
      _ = ∑ j ∈ Finset.Ico height (N + 1),
            (cubeScaleFactor Q *
              Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 := by
        congr 1
        ext j
        simp [Finset.mem_Ico, and_comm]
      _ = ∑ j ∈ Finset.Ico height (N + 1),
            (cubeScaleFactor Q) ^ 2 * r ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact boundaryFiniteHeightTailWeight_sq Q s j
      _ = (cubeScaleFactor Q) ^ 2 *
          ∑ j ∈ Finset.Ico height (N + 1), r ^ j := by
        rw [Finset.mul_sum]
  have hsum : ∑ j ∈ Finset.Ico height (N + 1), r ^ j ≤
      r ^ height / (1 - r) := geom_sum_Ico_le_of_lt_one hr0 hr1
  have hsq : ∑ j ∈ Finset.range (N + 1),
          (if height ≤ j then
            cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))
          else 0) ^ 2 ≤
      (cubeScaleFactor Q) ^ 2 * (r ^ height / (1 - r)) := by
    rw [hsumEq]
    exact mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
  have hquot : 0 ≤ r ^ height / (1 - r) :=
    div_nonneg (pow_nonneg hr0 _) (sub_nonneg.mpr hr1.le)
  calc
    boundaryFiniteHeightTailCoeff Q s N height =
        Real.sqrt (∑ j ∈ Finset.range (N + 1),
          (if height ≤ j then
            cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))
          else 0) ^ 2) := rfl
    _ ≤ Real.sqrt ((cubeScaleFactor Q) ^ 2 * (r ^ height / (1 - r))) :=
      Real.sqrt_le_sqrt hsq
    _ = cubeScaleFactor Q * Real.sqrt (r ^ height / (1 - r)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (cubeScaleFactor_nonneg Q)]
    _ = _ := rfl

omit [NeZero d] in
/-- Finite-height interpolation of the positive scalar Besov seminorm.
The first term is paid by the scalar `L²` norm and the second by the finite
`B¹_{2,∞}` seminorm.  Increasing `height` moves mass from the second term to
the first and makes its coefficient geometrically small when `s < 1`. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_le_finiteHeight
    (Q : TriadicCube d) (s : ℝ) (N height : ℕ) (v : Vec d → ℝ)
    (hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s N v ≤
      boundaryFiniteHeightHeadCoeff s N height *
          cubeLpNorm Q (2 : ℝ≥0∞) v +
        boundaryFiniteHeightTailCoeff Q s N height *
          cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N v := by
  let X : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) v
  let Y : ℝ := cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N v
  let A : ℕ → ℝ := fun j =>
    if j < height then 2 * Real.rpow (3 : ℝ) (s * (j : ℝ)) else 0
  let B : ℕ → ℝ := fun j =>
    if height ≤ j then
      cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))
    else 0
  have hX : 0 ≤ X := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v
  have hY : 0 ≤ Y := cubeBesovPartialSeminormTop_nonneg Q 1 (2 : ℝ≥0∞) N v
  have hA : ∀ j ∈ Finset.range (N + 1), 0 ≤ A j := by
    intro j hj
    dsimp [A]
    split_ifs
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    · exact le_rfl
  have hB : ∀ j ∈ Finset.range (N + 1), 0 ≤ B j := by
    intro j hj
    dsimp [B]
    split_ifs
    · exact mul_nonneg (cubeScaleFactor_nonneg Q)
        (Real.rpow_nonneg (by norm_num) _)
    · exact le_rfl
  have hdepth : ∀ j ∈ Finset.range (N + 1),
      cubeBesovPositiveScalarDepthSeminorm Q s v j ≤ A j * X + B j * Y := by
    intro j hj
    by_cases hlow : j < height
    · have hL2 := cubeBesovPositiveScalarDepthSeminorm_le_l2 Q s v j hv
      dsimp [A, B, X]
      rw [ite_eq_left hlow, ite_eq_right (Nat.not_le_of_lt hlow)]
      simpa only [zero_mul, add_zero, mul_assoc] using! hL2
    · have hhigh : height ≤ j := Nat.le_of_not_gt hlow
      have hjY : cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) v j ≤ Y := by
        dsimp [Y]
        unfold cubeBesovPartialSeminormTop
        exact Finset.le_sup' (s := Finset.range (N + 1))
          (f := fun k => cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) v k) hj
      rw [positiveScalarDepthSeminorm_eq_geometric_mul_one,
        positiveScalarDepthSeminorm_one_eq_scale_mul_depthSeminorm]
      dsimp [A, B]
      rw [ite_eq_right hlow, ite_eq_left hhigh, zero_mul, zero_add]
      have hcoeff : 0 ≤ cubeScaleFactor Q *
          Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) :=
        mul_nonneg (cubeScaleFactor_nonneg Q) (Real.rpow_nonneg (by norm_num) _)
      calc
        Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) *
              (cubeScaleFactor Q * cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) v j)
            = (cubeScaleFactor Q *
                Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) *
                cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) v j := by ring
        _ ≤ (cubeScaleFactor Q *
                Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) * Y :=
          mul_le_mul_of_nonneg_left hjY hcoeff
  have hsq : ∑ j ∈ Finset.range (N + 1),
        (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2 ≤
      ∑ j ∈ Finset.range (N + 1), (A j * X + B j * Y) ^ 2 := by
    exact Finset.sum_le_sum fun j hj =>
      pow_le_pow_left₀ (cubeBesovPositiveScalarDepthSeminorm_nonneg Q s v j)
        (hdepth j hj) 2
  have htriangle := sqrt_sum_sq_add_le_sqrt (Finset.range (N + 1))
    (fun j => A j * X) (fun j => B j * Y)
    (fun j hj => mul_nonneg (hA j hj) hX)
    (fun j hj => mul_nonneg (hB j hj) hY)
  have hhead : Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j * X) ^ 2) =
      boundaryFiniteHeightHeadCoeff s N height * X := by
    have hfactor := sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) X A hX
    rw [show (∑ j ∈ Finset.range (N + 1), (A j * X) ^ 2) =
        ∑ j ∈ Finset.range (N + 1), (X * A j) ^ 2 by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [mul_comm]]
    simpa only [boundaryFiniteHeightHeadCoeff, A, mul_comm] using hfactor
  have htail : Real.sqrt (∑ j ∈ Finset.range (N + 1), (B j * Y) ^ 2) =
      boundaryFiniteHeightTailCoeff Q s N height * Y := by
    have hfactor := sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) Y B hY
    rw [show (∑ j ∈ Finset.range (N + 1), (B j * Y) ^ 2) =
        ∑ j ∈ Finset.range (N + 1), (Y * B j) ^ 2 by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [mul_comm]]
    simpa only [boundaryFiniteHeightTailCoeff, B, mul_comm] using hfactor
  calc
    cubeBesovPositiveScalarPartialSeminormTwo Q s N v =
        Real.sqrt (∑ j ∈ Finset.range (N + 1),
          (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2) := rfl
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j * X + B j * Y) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j * X) ^ 2) +
        Real.sqrt (∑ j ∈ Finset.range (N + 1), (B j * Y) ^ 2) := htriangle
    _ = boundaryFiniteHeightHeadCoeff s N height * X +
        boundaryFiniteHeightTailCoeff Q s N height * Y := by rw [hhead, htail]
    _ = _ := rfl

/-- The finite-height split in the actual nonzero boundary-datum carrier.
The fine coefficient is explicit and geometrically small; the coarse
remainder depends only on the normalized `L²` size of the datum. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_h1_le_finiteHeight
    (Q : TriadicCube d) (s : ℝ) (N height : ℕ)
    (u : H1Function (openCubeSet Q)) (hs : s < 1) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s N u.toFun ≤
      (cubeScaleFactor Q *
          Real.sqrt ((Real.rpow (3 : ℝ) (2 * (s - 1))) ^ height /
            (1 - Real.rpow (3 : ℝ) (2 * (s - 1)))) *
          cubeBesovW12EmbeddingConstant d) *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) +
      boundaryFiniteHeightHeadCoeff s N height *
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let w : H1Function (openCubeSet Q) :=
    u.addConst (-cubeAverage Q u.toFun)
  have hwfun : w.toFun = cubeFluctuation Q u.toFun := by
    funext x
    simp [w, cubeFluctuation, sub_eq_add_neg]
  have hwgrad : w.grad = u.grad := by
    funext x
    exact H1Function.grad_addConst u (-cubeAverage Q u.toFun) x
  have hmem : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro j hj R hR
    exact memLp_on_descendant_of_memLp_generic (E := ℝ) hR
      u.memL2_normalizedCubeMeasure
  have hseminormEq :
      cubeBesovPositiveScalarPartialSeminormTwo Q s N u.toFun =
        cubeBesovPositiveScalarPartialSeminormTwo Q s N w.toFun := by
    have heq := cubeBesovPositiveScalarPartialSeminormTwo_sub_const
      Q s N u.toFun (cubeAverage Q u.toFun) hmem
    simpa only [hwfun, cubeFluctuation] using! heq.symm
  have hsplit := cubeBesovPositiveScalarPartialSeminormTwo_le_finiteHeight
    Q s N height w.toFun w.memL2_normalizedCubeMeasure
  have htail := boundaryFiniteHeightTailCoeff_le_geometric Q s N height hs
  have hW := cubeBesovPartialSeminormTop_one_two_le_normalizedW1pSeminorm
    Q N (boundaryH1ToW12 w)
  rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad] at hW
  have htailW :
      boundaryFiniteHeightTailCoeff Q s N height *
          cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N w.toFun ≤
        (cubeScaleFactor Q *
            Real.sqrt ((Real.rpow (3 : ℝ) (2 * (s - 1))) ^ height /
              (1 - Real.rpow (3 : ℝ) (2 * (s - 1)))) *
            cubeBesovW12EmbeddingConstant d) *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (w.grad x)) := by
    have hseminorm0 : 0 ≤ cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N w.toFun :=
      cubeBesovPartialSeminormTop_nonneg Q 1 (2 : ℝ≥0∞) N w.toFun
    calc
      boundaryFiniteHeightTailCoeff Q s N height *
          cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N w.toFun
          ≤ (cubeScaleFactor Q *
              Real.sqrt ((Real.rpow (3 : ℝ) (2 * (s - 1))) ^ height /
                (1 - Real.rpow (3 : ℝ) (2 * (s - 1))))) *
              cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N w.toFun :=
        mul_le_mul_of_nonneg_right htail hseminorm0
      _ ≤ (cubeScaleFactor Q *
              Real.sqrt ((Real.rpow (3 : ℝ) (2 * (s - 1))) ^ height /
                (1 - Real.rpow (3 : ℝ) (2 * (s - 1))))) *
              (cubeBesovW12EmbeddingConstant d *
                cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (w.grad x))) := by
        exact mul_le_mul_of_nonneg_left hW
          (mul_nonneg (cubeScaleFactor_nonneg Q) (Real.sqrt_nonneg _))
      _ = _ := by ring
  calc
    cubeBesovPositiveScalarPartialSeminormTwo Q s N u.toFun =
        cubeBesovPositiveScalarPartialSeminormTwo Q s N w.toFun := hseminormEq
    _ ≤
        boundaryFiniteHeightHeadCoeff s N height *
            cubeLpNorm Q (2 : ℝ≥0∞) w.toFun +
          boundaryFiniteHeightTailCoeff Q s N height *
            cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N w.toFun := hsplit
    _ ≤ boundaryFiniteHeightHeadCoeff s N height *
          cubeLpNorm Q (2 : ℝ≥0∞) w.toFun +
        (cubeScaleFactor Q *
            Real.sqrt ((Real.rpow (3 : ℝ) (2 * (s - 1))) ^ height /
              (1 - Real.rpow (3 : ℝ) (2 * (s - 1)))) *
            cubeBesovW12EmbeddingConstant d) *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (w.grad x)) :=
      add_le_add le_rfl htailW
    _ = _ := by
      rw [hwfun, hwgrad]
      ring

/-- Uniform-in-terminal-depth form of the preceding split. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_h1_le_finiteHeight_uniform
    (Q : TriadicCube d) (s : ℝ) (N height : ℕ)
    (u : H1Function (openCubeSet Q)) (hs : s < 1) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s N u.toFun ≤
      (cubeScaleFactor Q *
          Real.sqrt ((Real.rpow (3 : ℝ) (2 * (s - 1))) ^ height /
            (1 - Real.rpow (3 : ℝ) (2 * (s - 1)))) *
          cubeBesovW12EmbeddingConstant d) *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) +
      boundaryFiniteHeightHeadGlobalCoeff s height *
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) := by
  have hraw := cubeBesovPositiveScalarPartialSeminormTwo_h1_le_finiteHeight
    Q s N height u hs
  have hhead := boundaryFiniteHeightHeadCoeff_le_global s N height
  have hX : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) :=
    cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _
  exact hraw.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hhead hX))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
