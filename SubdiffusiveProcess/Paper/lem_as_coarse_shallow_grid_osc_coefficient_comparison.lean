import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- Exact pointwise exponential coefficient comparison after the coarse
constant has been separated. -/
theorem lem_as_coarse_shallow_grid_osc_coefficient_comparison
    (s a g0 g1 osc : ℝ) (hs : 0 < s) (ha : 0 ≤ a)
    (hdiff : |g1 - g0| ≤ osc) :
    (s * Real.exp (-osc)) * a ≤
        (s * Real.exp (g1 - g0)) * a ∧
      (s * Real.exp (g1 - g0)) * a ≤
        (s * Real.exp osc) * a := by
  rcases abs_le.mp hdiff with ⟨h_low, h_high⟩
  have h_exp_low : Real.exp (-osc) ≤ Real.exp (g1 - g0) := Real.exp_le_exp.mpr h_low
  have h_exp_high : Real.exp (g1 - g0) ≤ Real.exp osc := Real.exp_le_exp.mpr h_high
  have h_s_mul_low : s * Real.exp (-osc) ≤ s * Real.exp (g1 - g0) :=
    mul_le_mul_of_nonneg_left h_exp_low hs.le
  have h_s_mul_high : s * Real.exp (g1 - g0) ≤ s * Real.exp osc :=
    mul_le_mul_of_nonneg_left h_exp_high hs.le
  have h_final_low : (s * Real.exp (-osc)) * a ≤ (s * Real.exp (g1 - g0)) * a :=
    mul_le_mul_of_nonneg_right h_s_mul_low ha
  have h_final_high : (s * Real.exp (g1 - g0)) * a ≤ (s * Real.exp osc) * a :=
    mul_le_mul_of_nonneg_right h_s_mul_high ha
  exact And.intro h_final_low h_final_high

end Paper

