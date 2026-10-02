import SubdiffusiveProcess.Sobolev.HolderAffinePullback

/-! # Pointwise Hölder bounds from a normalized `C^α` norm

If the rescaled function `x ↦ U(z + r x) - c` has `C^α` norm at most `B` on the closed unit
cube and `U` is Hölder on `\overline{B(z, r/2)}`, then `|U x - U y| ≤ √d^α B (dist x y / r)^α`
there (sup-norm distance).  Nothing is claimed off the cube. -/

open Set MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess

/-- The Euclidean length is at most `√d` times the sup norm. -/
theorem euclidean_length_le_sqrt_card_mul_norm {d : ℕ} (x : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j) ^ 2) ≤ Real.sqrt d * ‖x‖ := by
  have h : ∑ j : Fin d, (x j) ^ 2 ≤ (d : ℝ) * ‖x‖ ^ 2 := by
    calc ∑ j : Fin d, (x j) ^ 2 ≤ ∑ _j : Fin d, ‖x‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          have hj : |x j| ≤ ‖x‖ := by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hj 2
      _ = (d : ℝ) * ‖x‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ j : Fin d, (x j) ^ 2) ≤ Real.sqrt ((d : ℝ) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt d * ‖x‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg x)]

/-- A normalized `C^α` bound on the unit cube gives a pointwise Hölder bound at scale `r`. -/
theorem abs_sub_le_of_normalized_cAlphaNorm {d : ℕ} (alpha : ℝ) (ha : 0 < alpha)
    (z : SpatialCoordinates d) (r cq B : ℝ) (hr : 0 < r) (U : SpatialCoordinates d → ℝ)
    (hU : IsHolderOn alpha (closure (Metric.ball z (r / 2))) U)
    (hB : cAlphaNorm alpha
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + r • x) - cq) ≤ B) :
    ∀ x ∈ closure (Metric.ball z (r / 2)), ∀ y ∈ closure (Metric.ball z (r / 2)),
      |U x - U y| ≤ Real.sqrt d ^ alpha * B * (dist x y / r) ^ alpha := by
  intro x hx y hy
  let S : Set (SpatialCoordinates d) :=
    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
  let F : SpatialCoordinates d → ℝ := fun w => U (z + r • w) - cq
  have hF : IsHolderOn alpha S F := isHolderOn_normalized_cube alpha z r cq hr U hU
  have hsup0 : 0 ≤ sSup {v : ℝ | ∃ w ∈ S, v = |F w|} := by
    apply Real.sSup_nonneg
    rintro v ⟨w, _, rfl⟩
    exact abs_nonneg _
  have hsemi_le : holderSeminorm alpha S F ≤ B := by
    have hle : holderSeminorm alpha S F ≤ cAlphaNorm alpha S F := by
      unfold cAlphaNorm
      linarith only [hsup0]
    exact hle.trans hB
  have hsemi0 : 0 ≤ holderSeminorm alpha S F := by
    apply Real.sSup_nonneg
    rintro v ⟨a, _, b, _, _, rfl⟩
    positivity
  have hB0 : 0 ≤ B := hsemi0.trans hsemi_le
  rw [closure_ball z (half_pos hr).ne'] at hx hy
  by_cases hxy : x = y
  · rw [hxy, sub_self, abs_zero]
    positivity
  let x' : SpatialCoordinates d := r⁻¹ • (x - z)
  let y' : SpatialCoordinates d := r⁻¹ • (y - z)
  have hmem : ∀ w ∈ Metric.closedBall z (r / 2), r⁻¹ • (w - z) ∈ S := by
    intro w hw
    change dist (r⁻¹ • (w - z)) 0 ≤ 1 / 2
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
      ← dist_eq_norm]
    rw [Metric.mem_closedBall] at hw
    calc r⁻¹ * dist w z ≤ r⁻¹ * (r / 2) := mul_le_mul_of_nonneg_left hw (inv_pos.mpr hr).le
      _ = 1 / 2 := by field_simp
  have hback : ∀ w : SpatialCoordinates d, z + r • (r⁻¹ • (w - z)) = w := by
    intro w
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  have hx'y' : x' ≠ y' := by
    intro h
    apply hxy
    rw [← hback x, ← hback y]
    exact congrArg (fun w => z + r • w) h
  have hdiff : F x' - F y' = U x - U y := by
    change (U (z + r • x') - cq) - (U (z + r • y') - cq) = U x - U y
    rw [hback x, hback y]
    ring
  let eu : ℝ := Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)
  have hsub : x' - y' ≠ 0 := sub_ne_zero.mpr hx'y'
  have heu_pos : 0 < eu := by
    obtain ⟨j, hj⟩ : ∃ j, (x' - y') j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hsub (funext hcon)
    apply Real.sqrt_pos.mpr
    have hjpos : 0 < (x' j - y' j) ^ 2 := by
      have : x' j - y' j ≠ 0 := by simpa only [Pi.sub_apply] using hj
      positivity
    exact lt_of_lt_of_le hjpos (Finset.single_le_sum (f := fun i => (x' i - y' i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have hratio : |F x' - F y'| / eu ^ alpha ≤ holderSeminorm alpha S F :=
    le_csSup hF ⟨x', hmem x hx, y', hmem y hy, hx'y', rfl⟩
  have hmain : |U x - U y| ≤ B * eu ^ alpha := by
    rw [← hdiff]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos heu_pos alpha)] at hratio
    exact hratio.trans (mul_le_mul_of_nonneg_right hsemi_le (Real.rpow_nonneg heu_pos.le _))
  have heu : eu ≤ Real.sqrt d * (dist x y / r) := by
    have h1 := euclidean_length_le_sqrt_card_mul_norm (x' - y')
    have h2 : ‖x' - y'‖ = dist x y / r := by
      rw [show x' - y' = r⁻¹ • (x - y) by
        simp only [x', y', ← smul_sub, sub_sub_sub_cancel_right]]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), dist_eq_norm]
      field_simp
    simpa only [Pi.sub_apply, h2] using h1
  calc |U x - U y| ≤ B * eu ^ alpha := hmain
    _ ≤ B * (Real.sqrt d * (dist x y / r)) ^ alpha :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow heu_pos.le heu ha.le) hB0
    _ = Real.sqrt d ^ alpha * B * (dist x y / r) ^ alpha := by
        rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity)]
        ring

end SubdiffusiveProcess
