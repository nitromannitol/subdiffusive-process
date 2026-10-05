module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- Numerical moment and threshold exponents with the strict slack needed
for the retained-grid union bound. -/
theorem lem_as_coarse_shallow_grid_exponent_choice
    (d : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    ∃ q eta : ℝ,
      1 ≤ q ∧ 0 < eta ∧ eta < rho ∧
        (d : ℝ) < q * (rho - eta) := by
  refine ⟨1 + 4 * (d : ℝ) / rho, rho / 2, ?_⟩
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hdiv : (0 : ℝ) < rho / 2 := div_pos hrho htwo
  have hqnonneg : 0 ≤ 4 * (d : ℝ) / rho :=
    div_nonneg (by positivity) hrho.le
  have hq : 1 ≤ 1 + 4 * (d : ℝ) / rho := by linarith
  have heta : 0 < rho / 2 := hdiv
  have heta_rho : rho / 2 < rho := by linarith
  have hidentity :
      (1 + 4 * (d : ℝ) / rho) * (rho - rho / 2) = rho / 2 + 2 * (d : ℝ) := by
    have hrho_ne : rho ≠ 0 := ne_of_gt hrho
    field_simp
    ring
  refine ⟨hq, heta, heta_rho, ?_⟩
  rw [hidentity]
  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  linarith

end SubdiffusiveProcess.Paper

