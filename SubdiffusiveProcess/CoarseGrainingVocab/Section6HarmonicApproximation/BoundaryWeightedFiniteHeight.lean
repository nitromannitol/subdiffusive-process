module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryFiniteHeightBesov
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryArbitraryH1Circ

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- Fine-depth coefficient when the target order is `t` and the available
positive regularity is `r`. -/
noncomputable def boundaryFiniteHeightTailBetweenCoeff
    (t r : ℝ) (N height : ℕ) : ℝ :=
  Real.sqrt <| ∑ j ∈ Finset.range (N + 1),
    (if height ≤ j then Real.rpow (3 : ℝ) ((t - r) * (j : ℝ)) else 0) ^ 2

/-- Terminal-depth-independent fine coefficient. -/
noncomputable def boundaryFiniteHeightTailBetweenGlobalCoeff
    (t r : ℝ) (height : ℕ) : ℝ :=
  Real.sqrt <| (Real.rpow (3 : ℝ) (2 * (t - r))) ^ height /
    (1 - Real.rpow (3 : ℝ) (2 * (t - r)))

theorem positiveScalarDepthSeminorm_eq_geometric_mul
    (Q : TriadicCube d) (t r : ℝ) (v : Vec d → ℝ) (j : ℕ) :
    cubeBesovPositiveScalarDepthSeminorm Q t v j =
      Real.rpow (3 : ℝ) ((t - r) * (j : ℝ)) *
        cubeBesovPositiveScalarDepthSeminorm Q r v j := by
  unfold cubeBesovPositiveScalarDepthSeminorm
  rw [← mul_assoc]
  congr 1
  calc
    Real.rpow (3 : ℝ) (t * (j : ℝ)) =
        Real.rpow (3 : ℝ) (((t - r) * (j : ℝ)) + r * (j : ℝ)) := by
          congr 1
          ring
    _ = Real.rpow (3 : ℝ) ((t - r) * (j : ℝ)) *
        Real.rpow (3 : ℝ) (r * (j : ℝ)) :=
      Real.rpow_add (by norm_num) _ _

theorem boundaryFiniteHeightTailBetweenCoeff_nonneg
    (t r : ℝ) (N height : ℕ) :
    0 ≤ boundaryFiniteHeightTailBetweenCoeff t r N height :=
  Real.sqrt_nonneg _

theorem boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg
    (t r : ℝ) (height : ℕ) :
    0 ≤ boundaryFiniteHeightTailBetweenGlobalCoeff t r height :=
  Real.sqrt_nonneg _

theorem boundaryFiniteHeightTailBetweenCoeff_le_global
    (t r : ℝ) (N height : ℕ) (htr : t < r) :
    boundaryFiniteHeightTailBetweenCoeff t r N height ≤
      boundaryFiniteHeightTailBetweenGlobalCoeff t r height := by
  let q : ℝ := Real.rpow (3 : ℝ) (2 * (t - r))
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hweight : ∀ j : ℕ,
      (Real.rpow (3 : ℝ) ((t - r) * (j : ℝ))) ^ 2 = q ^ j := by
    intro j
    calc
      (Real.rpow (3 : ℝ) ((t - r) * (j : ℝ))) ^ 2 =
          Real.rpow (Real.rpow (3 : ℝ) ((t - r) * (j : ℝ))) (2 : ℝ) := by
            exact (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (3 : ℝ) (((t - r) * (j : ℝ)) * 2) := by
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
              ((t - r) * (j : ℝ)) 2).symm
      _ = Real.rpow (3 : ℝ) (2 * (t - r) * (j : ℝ)) := by
            congr 1
            ring
      _ = Real.rpow q (j : ℝ) := by
            dsimp [q]
            rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ = q ^ j := Real.rpow_natCast q j
  have hsumEq :
      ∑ j ∈ Finset.range (N + 1),
          (if height ≤ j then
            Real.rpow (3 : ℝ) ((t - r) * (j : ℝ)) else 0) ^ 2 =
        ∑ j ∈ Finset.Ico height (N + 1), q ^ j := by
    calc
      _ = ∑ j ∈ (Finset.range (N + 1)).filter (fun j => height ≤ j),
          (Real.rpow (3 : ℝ) ((t - r) * (j : ℝ))) ^ 2 := by
            simp [Finset.sum_filter]
      _ = ∑ j ∈ Finset.Ico height (N + 1),
          (Real.rpow (3 : ℝ) ((t - r) * (j : ℝ))) ^ 2 := by
            congr 1
            ext j
            simp [Finset.mem_Ico, and_comm]
      _ = ∑ j ∈ Finset.Ico height (N + 1), q ^ j := by
            exact Finset.sum_congr rfl fun j _ => hweight j
  have hsum : ∑ j ∈ Finset.Ico height (N + 1), q ^ j ≤
      q ^ height / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 hq1
  unfold boundaryFiniteHeightTailBetweenCoeff
    boundaryFiniteHeightTailBetweenGlobalCoeff
  rw [hsumEq]
  exact Real.sqrt_le_sqrt hsum

/-- The global fine coefficient tends to zero with the splitting height. -/
theorem tendsto_boundaryFiniteHeightTailBetweenGlobalCoeff
    (t r : ℝ) (htr : t < r) :
    Filter.Tendsto
      (fun height : ℕ => boundaryFiniteHeightTailBetweenGlobalCoeff t r height)
      Filter.atTop (nhds 0) := by
  let q : ℝ := Real.rpow (3 : ℝ) (2 * (t - r))
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : Filter.Tendsto (fun height : ℕ => q ^ height)
      Filter.atTop (nhds 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hden : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hquot : Filter.Tendsto (fun height : ℕ => q ^ height / (1 - q))
      Filter.atTop (nhds 0) := by
    simpa [hden] using! hpow.div_const (1 - q)
  have hsqrt := hquot.sqrt
  simpa only [boundaryFiniteHeightTailBetweenGlobalCoeff, q, Real.sqrt_zero] using! hsqrt

/-- Quantitative height choice: any fixed nonnegative prefactor times the
fine coefficient can be made smaller than a prescribed positive budget. -/
theorem exists_height_mul_boundaryFiniteHeightTailBetweenGlobalCoeff_le
    (t r K eps : ℝ) (htr : t < r) (heps : 0 < eps) :
    ∃ height : ℕ,
      K * boundaryFiniteHeightTailBetweenGlobalCoeff t r height ≤ eps := by
  have htend := (tendsto_boundaryFiniteHeightTailBetweenGlobalCoeff t r htr).const_mul K
  have hev : ∀ᶠ height : ℕ in Filter.atTop,
      K * boundaryFiniteHeightTailBetweenGlobalCoeff t r height < eps := by
    exact (tendsto_order.1 (by simpa using! htend)).2 eps heps
  obtain ⟨height, hheight⟩ := Filter.eventually_atTop.1 hev
  exact ⟨height, (hheight height le_rfl).le⟩

/-- Finite-height interpolation between two positive orders.  Coarse depths
are paid by `L²`; fine depths are paid by a uniform bound at the larger
positive order. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_le_finiteHeight_between
    (Q : TriadicCube d) (t r : ℝ) (N height : ℕ) (v : Vec d → ℝ)
    (hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (htr : t < r) {Br : ℝ} (hBr : 0 ≤ Br)
    (hr : ∀ j ∈ Finset.range (N + 1),
      cubeBesovPositiveScalarDepthSeminorm Q r v j ≤ Br) :
    cubeBesovPositiveScalarPartialSeminormTwo Q t N v ≤
      boundaryFiniteHeightHeadGlobalCoeff t height *
          cubeLpNorm Q (2 : ℝ≥0∞) v +
        boundaryFiniteHeightTailBetweenGlobalCoeff t r height * Br := by
  let X := cubeLpNorm Q (2 : ℝ≥0∞) v
  let A : ℕ → ℝ := fun j =>
    if j < height then 2 * Real.rpow (3 : ℝ) (t * (j : ℝ)) else 0
  let B : ℕ → ℝ := fun j =>
    if height ≤ j then Real.rpow (3 : ℝ) ((t - r) * (j : ℝ)) else 0
  have hX : 0 ≤ X := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v
  have hA : ∀ j ∈ Finset.range (N + 1), 0 ≤ A j := by
    intro j hj
    dsimp [A]
    split_ifs
    · positivity
    · exact le_rfl
  have hB : ∀ j ∈ Finset.range (N + 1), 0 ≤ B j := by
    intro j hj
    dsimp [B]
    split_ifs
    · exact Real.rpow_nonneg (by norm_num) _
    · exact le_rfl
  have hdepth : ∀ j ∈ Finset.range (N + 1),
      cubeBesovPositiveScalarDepthSeminorm Q t v j ≤ A j * X + B j * Br := by
    intro j hj
    by_cases hlow : j < height
    · have hL2 := cubeBesovPositiveScalarDepthSeminorm_le_l2 Q t v j hv
      dsimp [A, B, X]
      rw [ite_eq_left hlow, ite_eq_right (Nat.not_le_of_lt hlow)]
      simpa only [zero_mul, add_zero, mul_assoc] using! hL2
    · have hhigh : height ≤ j := Nat.le_of_not_gt hlow
      rw [positiveScalarDepthSeminorm_eq_geometric_mul Q t r v j]
      dsimp [A, B]
      rw [ite_eq_right hlow, ite_eq_left hhigh, zero_mul, zero_add]
      exact mul_le_mul_of_nonneg_left (hr j hj)
        (Real.rpow_nonneg (by norm_num) _)
  have hsq : ∑ j ∈ Finset.range (N + 1),
        (cubeBesovPositiveScalarDepthSeminorm Q t v j) ^ 2 ≤
      ∑ j ∈ Finset.range (N + 1), (A j * X + B j * Br) ^ 2 :=
    Finset.sum_le_sum fun j hj =>
      pow_le_pow_left₀ (cubeBesovPositiveScalarDepthSeminorm_nonneg Q t v j)
        (hdepth j hj) 2
  have htriangle := sqrt_sum_sq_add_le_sqrt (Finset.range (N + 1))
    (fun j => A j * X) (fun j => B j * Br)
    (fun j hj => mul_nonneg (hA j hj) hX)
    (fun j hj => mul_nonneg (hB j hj) hBr)
  have hhead : Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j * X) ^ 2) ≤
      boundaryFiniteHeightHeadGlobalCoeff t height * X := by
    rw [show (∑ j ∈ Finset.range (N + 1), (A j * X) ^ 2) =
        ∑ j ∈ Finset.range (N + 1), (X * A j) ^ 2 by
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]]
    rw [sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) X A hX]
    simpa only [A, boundaryFiniteHeightHeadCoeff, mul_comm] using
      mul_le_mul_of_nonneg_right
        (boundaryFiniteHeightHeadCoeff_le_global t N height) hX
  have htail : Real.sqrt (∑ j ∈ Finset.range (N + 1), (B j * Br) ^ 2) ≤
      boundaryFiniteHeightTailBetweenGlobalCoeff t r height * Br := by
    rw [show (∑ j ∈ Finset.range (N + 1), (B j * Br) ^ 2) =
        ∑ j ∈ Finset.range (N + 1), (Br * B j) ^ 2 by
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]]
    rw [sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) Br B hBr]
    simpa only [B, boundaryFiniteHeightTailBetweenCoeff, mul_comm] using
      mul_le_mul_of_nonneg_right
        (boundaryFiniteHeightTailBetweenCoeff_le_global t r N height htr) hBr
  calc
    cubeBesovPositiveScalarPartialSeminormTwo Q t N v =
        Real.sqrt (∑ j ∈ Finset.range (N + 1),
          (cubeBesovPositiveScalarDepthSeminorm Q t v j) ^ 2) := rfl
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j * X + B j * Br) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j * X) ^ 2) +
        Real.sqrt (∑ j ∈ Finset.range (N + 1), (B j * Br) ^ 2) := htriangle
    _ ≤ boundaryFiniteHeightHeadGlobalCoeff t height * X +
        boundaryFiniteHeightTailBetweenGlobalCoeff t r height * Br :=
      add_le_add hhead htail

/-- The useful specialization of the preceding split.  Full-dual Poincare
prices the fine `B^(1-t)` depths by the gradient `circ` norm at exponent `t`.
Thus the high-frequency coefficient can be made small without a pointwise
lower ellipticity bound. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_h1_le_weightedFiniteHeight
    [NeZero d] (Q : TriadicCube d) (t : ℝ) (N height : ℕ)
    (u : H1Function (openCubeSet Q))
    (ht : 0 < t) (htHalf : t < 1 / 2) {Bcirc : ℝ}
    (hBcirc : 0 ≤ Bcirc)
    (hcirc : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x => u.grad x i) ≤ Bcirc) :
    let C := fullVectorPoincareCubeConstant Q
    let Br := cubeBesovScaleWeight (-(1 - t)) Q *
      ((C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) * Bcirc))
    cubeBesovPositiveScalarPartialSeminormTwo Q t N
        (cubeFluctuation Q u.toFun) ≤
      boundaryFiniteHeightHeadGlobalCoeff t height *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) +
        boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br := by
  dsimp only
  let v := cubeFluctuation Q u.toFun
  let G := u.grad
  let C := fullVectorPoincareCubeConstant Q
  let Br := cubeBesovScaleWeight (-(1 - t)) Q *
    ((C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Bcirc))
  have hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure.sub (memLp_const (cubeAverage Q u.toFun))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact fullVectorPoincareCubeConstant_nonneg Q
  have hG : ∀ i : Fin d,
      MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact u.grad_memL2_normalizedCubeMeasure i
  have hBr : 0 ≤ Br := by
    dsimp [Br]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) Q)
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg (by positivity) hBcirc))
  have hhigh : ∀ j ∈ Finset.range (N + 1),
      cubeBesovPositiveScalarDepthSeminorm Q (1 - t) v j ≤ Br := by
    intro j hj
    have hfull := boundaryH1_fullDualPoincare Q u N
    have hlocal : CubeLocalFullCircPoincareVectorEstimate Q
        (C * (3 : ℝ) ^ ((d : ℝ) + 1)) v G N := by
      simpa only [C, v, G] using! hfull.to_localFullCircEstimate hG hC
    have hdepth : cubeBesovDepthSeminorm Q (1 - t) (2 : ℝ≥0∞) v j ≤
        (C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ∑ i : Fin d,
            cubeBesovCircNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => G x i) := by
      have hraw :=
        cubeBesovDepthSeminorm_two_le_sum_circNorm_of_vector_local_full_circ_bound
          Q (1 - t) (C * (3 : ℝ) ^ ((d : ℝ) + 1)) v G j
            (by linarith) (by linarith)
            (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
            hG (by intro R hR; exact hlocal j hj R hR)
      simpa only [sub_sub_cancel] using! hraw
    have hnorm : ∀ i : Fin d,
        cubeBesovCircNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i) ≤
          Bcirc := by
      intro i
      exact cubeBesovCircNorm_le_of_forall_partialNorm_le
        Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i)
          (by norm_num) (hcirc i)
    have hsum : ∑ i : Fin d,
          cubeBesovCircNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i) ≤
        (Fintype.card (Fin d) : ℝ) * Bcirc := by
      calc
        _ ≤ ∑ _i : Fin d, Bcirc := Finset.sum_le_sum fun i _ => hnorm i
        _ = (Fintype.card (Fin d) : ℝ) * Bcirc := by simp
    rw [cubeBesovPositiveScalarDepthSeminorm_eq_scaleWeight_neg_mul_cubeBesovDepthSeminorm_two]
    exact (mul_le_mul_of_nonneg_left
      (hdepth.trans (mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))))
      (cubeBesovScaleWeight_nonneg (-(1 - t)) Q)).trans_eq (by
        dsimp [Br])
  have hsplit := cubeBesovPositiveScalarPartialSeminormTwo_le_finiteHeight_between
    Q t (1 - t) N height v hv (by linarith) hBr hhigh
  simpa only [v, Br, C] using! hsplit

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
