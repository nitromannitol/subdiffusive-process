import SubdiffusiveProcess.Paper.lfgc_chain_cover

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Numerical lemmas for the single-point chain

Existence of small oscillation tolerances for the transfer inequalities, and the
geometric bookkeeping of the chain increments.
-/

open Real

namespace Paper
theorem aux_lfgc_single_num_exp_sub_one_le_two_mul {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : Real.exp ε - 1 ≤ 2 * ε := by
  have hq := Real.abs_exp_sub_one_le (show |ε| ≤ 1 by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg (by linarith [Real.one_le_exp h0]), abs_of_nonneg h0] at hq
  exact hq

theorem aux_lfgc_single_num_tolSlack_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    aux_lfgc_root_impl_tolSlack ε ≤ 4 * ε + 2 * Real.sqrt ε := by
  unfold aux_lfgc_root_impl_tolSlack
  have he := aux_lfgc_single_num_exp_sub_one_le_two_mul h0 h1
  have he0 : 0 ≤ Real.exp ε - 1 := by linarith [Real.one_le_exp h0]
  have hs : Real.sqrt (2 * (Real.exp ε - 1)) ≤ 2 * Real.sqrt ε := by
    calc Real.sqrt (2 * (Real.exp ε - 1)) ≤ Real.sqrt (4 * ε) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt ε := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith

/-- A tolerance with slack below a prescribed margin. -/
theorem lfgc_single_num {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ aux_lfgc_root_impl_tolSlack ε ≤ η := by
  refine ⟨min 1 (η ^ 2 / 64), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  set ε := min 1 (η ^ 2 / 64)
  have h0 : 0 ≤ ε := le_min zero_le_one (by positivity)
  have h1 : ε ≤ 1 := min_le_left _ _
  have h2 : ε ≤ η ^ 2 / 64 := min_le_right _ _
  refine (aux_lfgc_single_num_tolSlack_le h0 h1).trans ?_
  have hs : Real.sqrt ε ≤ η / 8 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hε : 4 * ε ≤ η / 2 := by
    rcases le_or_gt η 1 with hη1 | hη1
    · nlinarith
    · nlinarith [h1]
  linarith

end Paper
