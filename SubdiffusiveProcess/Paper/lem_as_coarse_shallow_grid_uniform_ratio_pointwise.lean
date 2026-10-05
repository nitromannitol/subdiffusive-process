module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- Elementary deterministic domination of a positive normalized ratio. -/
theorem lem_as_coarse_shallow_grid_uniform_ratio_pointwise
    (a E g : ℝ) (ha : 1 ≤ a) (hE : a ≤ E) :
    a * Real.exp g + a⁻¹ * Real.exp (-g) ≤
      E * (Real.exp g + Real.exp (-g)) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have haE : 1 ≤ E := le_trans ha hE
  have hEg : 0 ≤ Real.exp g := le_of_lt (Real.exp_pos g)
  have hEng : 0 ≤ Real.exp (-g) := le_of_lt (Real.exp_pos (-g))
  have hinv : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
  have h1 : a * Real.exp g ≤ E * Real.exp g :=
    mul_le_mul_of_nonneg_right hE hEg
  have h2 : a⁻¹ * Real.exp (-g) ≤ E * Real.exp (-g) :=
    le_trans (mul_le_mul_of_nonneg_right hinv hEng)
      (mul_le_mul_of_nonneg_right haE hEng)
  calc
    a * Real.exp g + a⁻¹ * Real.exp (-g)
        ≤ E * Real.exp g + E * Real.exp (-g) := add_le_add h1 h2
    _ = E * (Real.exp g + Real.exp (-g)) := by ring

end SubdiffusiveProcess.Paper
