module

public import SubdiffusiveProcess.Compactness.OperatorConvergence

@[expose] public section

open Filter Set
open scoped Topology
/-! Dense quadratic tests determine Cauchy matrix elements under a uniform operator bound.
The model response estimates and the source of that bound remain separate. -/

namespace SubdiffusiveProcess

theorem cauchySeq_inner_of_dense_quadratic_responses
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ℕ → H →L[ℝ] H} {D : Set H}
    (hD : Dense D)
    (hadd : ∀ x ∈ D, ∀ y ∈ D, x + y ∈ D)
    (hsym : ∀ n : ℕ, ∀ x y : H, inner ℝ (T n x) y = inner ℝ x (T n y))
    (hbound : ∃ C : ℝ, ∀ n : ℕ, ‖T n‖ ≤ C)
    (hq : ∀ x ∈ D, CauchySeq (fun n => inner ℝ x (T n x))) :
    ∀ x y : H, CauchySeq (fun n => inner ℝ (T n x) y) := by
  obtain ⟨C, hC⟩ := hbound
  have hC0 : 0 ≤ C := (norm_nonneg (T 0)).trans (hC 0)
  have hpair_bound (n : ℕ) (x y : H) :
      ‖inner ℝ (T n x) y‖ ≤ C * ‖x‖ * ‖y‖ := by
    calc
      ‖inner ℝ (T n x) y‖ ≤ ‖T n x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (‖T n‖ * ‖x‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ((T n).le_opNorm x) (norm_nonneg y)
      _ ≤ (C * ‖x‖) * ‖y‖ := by
        gcongr
        exact hC n
  have hmixed_D {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
      CauchySeq (fun n => inner ℝ (T n x) y) := by
    have hsum := hq (x + y) (hadd x hx y hy)
    have hxq := hq x hx
    have hyq := hq y hy
    have hc0 : CauchySeq (fun n =>
        inner ℝ (x + y) (T n (x + y)) -
          inner ℝ x (T n x) - inner ℝ y (T n y)) :=
      (hsum.add hxq.neg).add hyq.neg
    have hc : CauchySeq (fun n =>
        (2 : ℝ)⁻¹ *
          (inner ℝ (x + y) (T n (x + y)) -
            inner ℝ x (T n x) - inner ℝ y (T n y))) := by
      simpa only [Function.comp_def, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul] using
        (((2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ ℝ).lipschitzWith.cauchySeq_comp hc0)
    convert hc using 1
    funext n
    have hs : inner ℝ y (T n x) = inner ℝ (T n x) y := by
      rw [real_inner_comm]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hs,
      ← hsym n x y]
    ring
  have hmixed_left {x : H} (hx : x ∈ D) (y : H) :
      CauchySeq (fun n => inner ℝ (T n x) y) := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    let δ : ℝ := ε / (3 * (C * ‖x‖ + 1))
    have hden : 0 < 3 * (C * ‖x‖ + 1) := by positivity
    have hδ : 0 < δ := div_pos hε hden
    have hsmall {d : ℝ} (hd0 : 0 ≤ d) (hd : d < δ) :
        C * ‖x‖ * d < ε / 3 := by
      have hA : 0 ≤ C * ‖x‖ := mul_nonneg hC0 (norm_nonneg x)
      calc
        C * ‖x‖ * d ≤ (C * ‖x‖ + 1) * d := by
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hd0
        _ < (C * ‖x‖ + 1) * δ := mul_lt_mul_of_pos_left hd (by linarith)
        _ = ε / 3 := by
          dsimp [δ]
          field_simp
    obtain ⟨z, hzD, hyz⟩ := hD.exists_dist_lt y hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hmixed_D hx hzD) (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hm_err : ‖inner ℝ (T m x) (y - z)‖ < ε / 3 := by
      calc
        ‖inner ℝ (T m x) (y - z)‖ ≤ C * ‖x‖ * ‖y - z‖ := hpair_bound m x (y - z)
        _ = C * ‖x‖ * dist y z := by rw [dist_eq_norm]
        _ < ε / 3 := hsmall (dist_nonneg) hyz
    have hn_err : ‖inner ℝ (T n x) (y - z)‖ < ε / 3 := by
      calc
        ‖inner ℝ (T n x) (y - z)‖ ≤ C * ‖x‖ * ‖y - z‖ := hpair_bound n x (y - z)
        _ = C * ‖x‖ * dist y z := by rw [dist_eq_norm]
        _ < ε / 3 := hsmall (dist_nonneg) hyz
    have hmid := hN m hm n hn
    rw [Real.dist_eq] at hmid ⊢
    calc
      |inner ℝ (T m x) y - inner ℝ (T n x) y|
          ≤ ‖inner ℝ (T m x) (y - z)‖ +
              |inner ℝ (T m x) z - inner ℝ (T n x) z| +
              ‖inner ℝ (T n x) (y - z)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs]
            rw [inner_sub_right, inner_sub_right]
            calc
              |inner ℝ (T m x) y - inner ℝ (T n x) y|
                  ≤ |inner ℝ (T m x) y - inner ℝ (T m x) z| +
                      |inner ℝ (T m x) z - inner ℝ (T n x) y| :=
                    abs_sub_le _ _ _
              _ ≤ |inner ℝ (T m x) y - inner ℝ (T m x) z| +
                    (|inner ℝ (T m x) z - inner ℝ (T n x) z| +
                      |inner ℝ (T n x) z - inner ℝ (T n x) y|) :=
                    by
                      gcongr
                      exact abs_sub_le _ _ _
              _ = _ := by rw [abs_sub_comm (inner ℝ (T n x) z)]; ring
      _ < ε := by linarith
  intro x y
  refine Metric.cauchySeq_iff.2 fun ε hε => ?_
  let δ : ℝ := ε / (3 * (C * ‖y‖ + 1))
  have hden : 0 < 3 * (C * ‖y‖ + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hsmall {d : ℝ} (hd0 : 0 ≤ d) (hd : d < δ) :
      C * d * ‖y‖ < ε / 3 := by
    have hA : 0 ≤ C * ‖y‖ := mul_nonneg hC0 (norm_nonneg y)
    calc
      C * d * ‖y‖ = (C * ‖y‖) * d := by ring
      _ ≤ (C * ‖y‖ + 1) * d := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hd0
      _ < (C * ‖y‖ + 1) * δ := mul_lt_mul_of_pos_left hd (by linarith)
      _ = ε / 3 := by
        dsimp [δ]
        field_simp
  obtain ⟨z, hzD, hxz⟩ := hD.exists_dist_lt x hδ
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hmixed_left hzD y) (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hm_err : ‖inner ℝ (T m (x - z)) y‖ < ε / 3 := by
    calc
      ‖inner ℝ (T m (x - z)) y‖ ≤ C * ‖x - z‖ * ‖y‖ := hpair_bound m (x - z) y
      _ = C * dist x z * ‖y‖ := by rw [dist_eq_norm]
      _ < ε / 3 := hsmall dist_nonneg hxz
  have hn_err : ‖inner ℝ (T n (x - z)) y‖ < ε / 3 := by
    calc
      ‖inner ℝ (T n (x - z)) y‖ ≤ C * ‖x - z‖ * ‖y‖ := hpair_bound n (x - z) y
      _ = C * dist x z * ‖y‖ := by rw [dist_eq_norm]
      _ < ε / 3 := hsmall dist_nonneg hxz
  have hmid := hN m hm n hn
  rw [Real.dist_eq] at hmid ⊢
  rw [map_sub] at hm_err hn_err
  calc
    |inner ℝ (T m x) y - inner ℝ (T n x) y|
        ≤ ‖inner ℝ (T m x - T m z) y‖ +
            |inner ℝ (T m z) y - inner ℝ (T n z) y| +
            ‖inner ℝ (T n x - T n z) y‖ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          rw [inner_sub_left, inner_sub_left]
          calc
            |inner ℝ (T m x) y - inner ℝ (T n x) y|
                ≤ |inner ℝ (T m x) y - inner ℝ (T m z) y| +
                    |inner ℝ (T m z) y - inner ℝ (T n x) y| :=
                  abs_sub_le _ _ _
            _ ≤ |inner ℝ (T m x) y - inner ℝ (T m z) y| +
                  (|inner ℝ (T m z) y - inner ℝ (T n z) y| +
                    |inner ℝ (T n z) y - inner ℝ (T n x) y|) :=
                  by
                    gcongr
                    exact abs_sub_le _ _ _
            _ = _ := by rw [abs_sub_comm (inner ℝ (T n z) y)]; ring
    _ < ε := by linarith

end SubdiffusiveProcess
