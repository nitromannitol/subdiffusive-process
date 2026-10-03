module

public import SubdiffusiveProcess.Variational.DualEnergy
public import Mathlib.Analysis.InnerProductSpace.StarOrder
@[expose] public section

open Filter Set
open scoped Topology

/-! A positive shift of a bounded nonnegative symmetric operator has a unique
bounded inverse on the original real Hilbert space. -/

namespace SubdiffusiveProcess

theorem existsUnique_positive_shift_inverse
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (G : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : H, 0 ≤ inner ℝ x (G x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃! R : H →L[ℝ] H,
      (G + ε • ContinuousLinearMap.id ℝ H).comp R = ContinuousLinearMap.id ℝ H ∧
      R.comp (G + ε • ContinuousLinearMap.id ℝ H) = ContinuousLinearMap.id ℝ H ∧
      (∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y)) ∧
      (∀ x : H, 0 ≤ inner ℝ x (R x)) ∧ ‖R‖ ≤ 1 / ε := by
  let A : H →L[ℝ] H := G + ε • ContinuousLinearMap.id ℝ H
  have hA_coercive (x : H) : ε * ‖x‖ ^ 2 ≤ inner ℝ (A x) x := by
    change ε * ‖x‖ ^ 2 ≤ inner ℝ (G x + ε • x) x
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hp : 0 ≤ inner ℝ (G x) x := by
      rw [hsym x x]
      exact hpos x
    linarith
  have hunit : IsUnit A := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map A
      (c := ⟨ε, hε.le⟩) (by exact_mod_cast hε)
    intro x
    change ‖x‖ ^ 2 * ε ≤ ‖inner ℝ (A x) x‖
    simpa [mul_comm, Real.norm_eq_abs] using
      (hA_coercive x).trans (le_abs_self (inner ℝ (A x) x))
  let R : H →L[ℝ] H := Ring.inverse A
  have hAR : A.comp R = ContinuousLinearMap.id ℝ H := by
    change A * R = 1
    exact Ring.mul_inverse_cancel A hunit
  have hRA : R.comp A = ContinuousLinearMap.id ℝ H := by
    change R * A = 1
    exact Ring.inverse_mul_cancel A hunit
  have hA_symm (x y : H) : inner ℝ (A x) y = inner ℝ x (A y) := by
    dsimp [A]
    change inner ℝ (G x + ε • x) y = inner ℝ x (G y + ε • y)
    simp only [inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hsym]
  have hR_symm (x y : H) : inner ℝ (R x) y = inner ℝ x (R y) := by
    calc
      inner ℝ (R x) y = inner ℝ (R x) (A (R y)) := by
        have hy := DFunLike.congr_fun hAR y
        simpa using congrArg (inner ℝ (R x)) hy.symm
      _ = inner ℝ (A (R x)) (R y) := (hA_symm (R x) (R y)).symm
      _ = inner ℝ x (R y) := by
        have hx := DFunLike.congr_fun hAR x
        simpa using congrArg (fun z ↦ inner ℝ z (R y)) hx
  have hR_pos (x : H) : 0 ≤ inner ℝ x (R x) := by
    have hx := DFunLike.congr_fun hAR x
    have hc := hA_coercive (R x)
    rw [show A (R x) = x by simpa using hx] at hc
    nlinarith [sq_nonneg ‖R x‖]
  have hR_bound : ‖R‖ ≤ 1 / ε := by
    apply R.opNorm_le_bound (by positivity)
    intro x
    by_cases hx : R x = 0
    · rw [hx, norm_zero]
      exact mul_nonneg (div_nonneg zero_le_one hε.le) (norm_nonneg x)
    have hnpos : 0 < ‖R x‖ := norm_pos_iff.mpr hx
    have hco := hA_coercive (R x)
    have heq : A (R x) = x := by
      simpa using DFunLike.congr_fun hAR x
    rw [heq] at hco
    have hcs : inner ℝ x (R x) ≤ ‖x‖ * ‖R x‖ := by
      exact (le_abs_self _).trans (by
        simpa [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) x (R x)))
    rw [show 1 / ε * ‖x‖ = ‖x‖ / ε by field_simp]
    apply (le_div_iff₀ hε).2
    nlinarith
  refine ⟨R, ?_, ?_⟩
  · exact ⟨hAR, hRA, hR_symm, hR_pos, hR_bound⟩
  · intro S hS
    calc
      S = (ContinuousLinearMap.id ℝ H).comp S := by simp
      _ = (R.comp A).comp S := by rw [hRA]
      _ = R.comp (A.comp S) := by rw [ContinuousLinearMap.comp_assoc]
      _ = R.comp (ContinuousLinearMap.id ℝ H) := by rw [hS.1]
      _ = R := by simp


end SubdiffusiveProcess
