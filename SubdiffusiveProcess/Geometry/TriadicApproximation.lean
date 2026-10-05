module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Choose a triadic mesh fine enough for a prescribed approximation error.
This is a deterministic scale choice, without analytic or probabilistic content. -/

open Filter

namespace SubdiffusiveProcess

/-- A triadic side can simultaneously be at most one and make a fixed linear error arbitrarily small. -/
theorem exists_triadic_side_error_lt (r B eps : ℝ) (heps : 0 < eps) :
    ∃ J : ℕ, r / (3 : ℝ) ^ J ≤ 1 ∧ B * (r / (3 : ℝ) ^ J) < eps := by
  have h3 : Tendsto (fun J : ℕ => (3 : ℝ) ^ J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨J, hJ⟩ := (h3.eventually_gt_atTop (max r (B * r / eps))).exists
  have hpow : (0 : ℝ) < (3 : ℝ) ^ J := by positivity
  refine ⟨J, (div_le_one hpow).mpr ((le_max_left _ _).trans hJ.le), ?_⟩
  rw [← mul_div_assoc, div_lt_iff₀ hpow]
  have hsmall := (le_max_right r (B * r / eps)).trans_lt hJ
  have hbound := (div_lt_iff₀ heps).mp hsmall
  simpa only [mul_comm eps] using hbound

end SubdiffusiveProcess
