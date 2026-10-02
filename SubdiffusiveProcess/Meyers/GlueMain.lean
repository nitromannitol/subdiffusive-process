import SubdiffusiveProcess.Meyers.Glue

/-! The `d ≥ 2` case: `E2Body` (the paper's derived form) from the exact Meyers estimate. -/

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

variable {d : ℕ}

/-- the constant of the glue -/
def glueConst (d : ℕ) (p C0 : ℝ) : ℝ :=
  (Fintype.card (Fin d → Fin (3 * d + 1)) : ℝ) * C0 *
    (unitMeanZeroPoincareConst d * 4 * (d : ℝ) * (2 ^ ((d : ℝ) / 2) * 2 ^ ((d : ℝ) / 2)) /
        (3 ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) * 2 ^ ((d : ℝ) / p)) + 2 ^ ((d : ℝ) / p) / 3)

theorem glueConst_pos (hd : 2 ≤ d) (p : ℝ) {C0 : ℝ} (hC0 : 0 < C0) : 0 < glueConst d p C0 := by
  unfold glueConst
  have hcard : (0 : ℝ) < (Fintype.card (Fin d → Fin (3 * d + 1)) : ℝ) := by
    have : 0 < Fintype.card (Fin d → Fin (3 * d + 1)) := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨fun _ => ⟨0, by omega⟩⟩
    exact_mod_cast this
  have hκ := unitMeanZeroPoincareConst_nonneg d
  have ha : 0 < (2 : ℝ) ^ ((d : ℝ) / p) := Real.rpow_pos_of_pos (by norm_num) _
  have hb : 0 < (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have he : 0 < (3 : ℝ) ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have : 0 ≤ unitMeanZeroPoincareConst d * 4 * (d : ℝ) * (2 ^ ((d : ℝ) / 2) * 2 ^ ((d : ℝ) / 2)) /
        (3 ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) * 2 ^ ((d : ℝ) / p)) := by positivity
  positivity

theorem e2_glue (hd : 2 ≤ d) {p epsilon C0 : ℝ} (hp : 2 ≤ p) (hC0 : 0 < C0)
    (hM : MeyersEstimate d p epsilon C0) : E2Body d p epsilon (glueConst d p C0) := by
  haveI : NeZero d := ⟨by omega⟩
  have hp0 : 0 < p := by linarith
  intro x0 l hl a a0 ha0 haM hnear F Kf hFM hKf hFb u heq
  haveI hfinQ : IsFiniteMeasure (volume.restrict (Metric.ball x0 (2 * l))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  -- mean subtraction
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = volumeAverage (Metric.ball x0 (2 * l)) u.toFun := ⟨_, rfl⟩
  let v : H1Function (Metric.ball x0 (2 * l)) := u.addConst (-c)
  have hvfun : v.toFun = fun y => u.toFun y - volumeAverage (Metric.ball x0 (2 * l)) u.toFun := by
    funext y
    rw [← hc]
    simp [v, sub_eq_add_neg]
  have hvgrad : v.grad = u.grad := by
    funext x
    exact H1Function.grad_addConst u (-c) x
  have heqv : ∀ phi : H10Function (Metric.ball x0 (2 * l)),
      (∫ x in Metric.ball x0 (2 * l), a x * (∑ i : Fin d, v.grad x i * phi.toH1Function.grad x i)) =
        ∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x := by
    intro phi
    rw [hvgrad]
    exact heq phi
  have hk := fun k => ball_bound hp hC0 hM x0 hl a ha0 haM hnear F Kf hFM hKf hFb v heqv k
  have hGv : (fun x => Real.sqrt (∑ i : Fin d, (v.grad x i) ^ 2)) =
      fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2) := by rw [hvgrad]
  simp only [hGv] at hk
  -- cube Poincaré
  have hPoin := eLpNorm_sub_average_le x0 (by positivity : 0 < 2 * l) u
  rw [← hvfun] at hPoin
  -- sum over the grid
  obtain ⟨hmem, hsum⟩ := sum_grid_bound x0 hl hp (memLp_two_gradNorm u) (fun k => (hk k).1)
  refine ⟨hmem, ?_⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℝ, A2 = (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) 2
      (volume.restrict (Metric.ball x0 (2 * l)))).toReal := ⟨_, rfl⟩
  rw [← hA2] at hPoin ⊢
  have hA2nn : 0 ≤ A2 := by rw [hA2]; exact ENNReal.toReal_nonneg
  have hBp : 0 ≤ (l / 3) ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) := Real.rpow_nonneg (by positivity) _
  have hV : volume.real (Metric.ball x0 (2 * l)) = (2 * (2 * l)) ^ d :=
    volume_real_ball x0 (by positivity)
  have hV1 : volume.real (Metric.ball x0 l) = (2 * l) ^ d := volume_real_ball x0 hl
  have hkk : ∀ k : Fin d → Fin (3 * d + 1),
      (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) (ENNReal.ofReal p)
        (volume.restrict (eBall (x0 + l • gridCenter d k) (l / 3)))).toReal ≤
      C0 * ((l / 3) ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) *
          (unitMeanZeroPoincareConst d * (2 * (2 * l)) * (d : ℝ) * A2)
        + (l / 3) * ((Kf / a0) * ((2 * (2 * l)) ^ d) ^ (1 / p))) := by
    intro k
    refine (hk k).2.trans ?_
    rw [hV]
    apply mul_le_mul_of_nonneg_left _ hC0.le
    exact add_le_add (mul_le_mul_of_nonneg_left hPoin hBp) le_rfl
  have hP : (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x0 l))).toReal ≤
      (Fintype.card (Fin d → Fin (3 * d + 1)) : ℝ) *
      (C0 * ((l / 3) ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) *
          (unitMeanZeroPoincareConst d * (2 * (2 * l)) * (d : ℝ) * A2)
        + (l / 3) * ((Kf / a0) * ((2 * (2 * l)) ^ d) ^ (1 / p)))) := by
    refine hsum.trans ((Finset.sum_le_sum fun k _ => hkk k).trans ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  obtain ⟨f1, f2, f3, f4⟩ := rpow_facts (p := p) d hl
  rw [f2] at hP
  rw [hV, hV1, f1, f3, ← mul_assoc (2 ^ ((d : ℝ) / 2))]
  have hs : 0 < (2 : ℝ) ^ ((d : ℝ) / p) := Real.rpow_pos_of_pos (by norm_num) _
  have ht : 0 < (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have he : 0 < (3 : ℝ) ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hL : 0 < l ^ ((d : ℝ) / p) := Real.rpow_pos_of_pos hl _
  have hM : 0 < l ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hl _
  have hcard : 0 ≤ (Fintype.card (Fin d → Fin (3 * d + 1)) : ℝ) := Nat.cast_nonneg _
  have := alg_step (a := (2 : ℝ) ^ ((d : ℝ) / p)) (b := 2 ^ ((d : ℝ) / 2) * 2 ^ ((d : ℝ) / 2))
    (e := 3 ^ ((d : ℝ) * (1 / p - 1 / 2) - 1)) (L := l ^ ((d : ℝ) / p)) (M := l ^ ((d : ℝ) / 2))
    (l := l) (a0 := a0) (A2 := A2) (Kf := Kf) (κ := unitMeanZeroPoincareConst d) (d' := (d : ℝ))
    (N := (Fintype.card (Fin d → Fin (3 * d + 1)) : ℝ)) (C0 := C0)
    (P := (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x0 l))).toReal)
    (Bp := (l / 3) ^ ((d : ℝ) * (1 / p - 1 / 2) - 1))
    hs (by positivity) he hL hM hl ha0 hA2nn hKf (unitMeanZeroPoincareConst_nonneg d)
    (Nat.cast_nonneg d) hcard hC0.le f4 hP
  unfold glueConst
  exact this

end SubdiffusiveProcess.Meyers
