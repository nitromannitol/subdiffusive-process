import SubdiffusiveProcess.Paper.lem_affine_exponent_limit

/-! Dimension-dependent affine exponents, chosen before all random data.
The existing exponent theorem is reused with a fixed trace exponent close
enough to one to preserve the preceding comparison estimates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess.Lane3

namespace Paper
noncomputable section

/-- The dimension-level choices approved in MATH-REVIEW Q1. -/
structure aux_thm_prop_AffineParameters (d : ℕ) where
  alpha : ℝ
  gamma : ℝ
  zeta : ℝ
  alpha_lower : (127 / 128 : ℝ) < alpha
  alpha_upper : alpha < 1
  gamma_lower : 0 < gamma
  gamma_upper : gamma < 1
  zeta_pos : 0 < zeta
  exponent_neg : affineExponent d alpha (127 / 128) gamma zeta < 0

/-- Existence is the already checked exponent-limit theorem, with no new
fixed-alpha feasibility claim. -/
theorem aux_thm_prop_affine_parameters_nonempty (d : ℕ) (hd : 2 ≤ d) :
    Nonempty (aux_thm_prop_AffineParameters d) := by
  obtain ⟨a, g, z, ha, ha1, hg, hg1, hz, hneg⟩ :=
    (lem_affine_exponent_limit d hd (127 / 128) (by norm_num) (by norm_num)).2.2.2
  exact ⟨⟨a, g, z, ha, ha1, hg, hg1, hz, hneg⟩⟩

/-- This one choice is shared by every affine-consuming catalogue. -/
def aux_thm_prop_affine_parameters (d : ℕ) (hd : 2 ≤ d) :
    aux_thm_prop_AffineParameters d :=
  Classical.choice (aux_thm_prop_affine_parameters_nonempty d hd)

def aux_thm_prop_alpha (d : ℕ) (hd : 2 ≤ d) : ℝ :=
  (aux_thm_prop_affine_parameters d hd).alpha

/-- The chosen alpha also satisfies the earlier density comparison margin;
its reference eta remains `1/128`. -/
theorem aux_thm_prop_alpha_bounds (d : ℕ) (hd : 2 ≤ d) :
    (1 / 2 : ℝ) < aux_thm_prop_alpha d hd ∧
    aux_thm_prop_alpha d hd < 1 ∧
    1 + (1 / 128 : ℝ) < 2 * aux_thm_prop_alpha d hd ∧
    2 * (1 - aux_thm_prop_alpha d hd) + (1 / 128 : ℝ) < (1 / 4 : ℝ) / 8 := by
  have hlo := (aux_thm_prop_affine_parameters d hd).alpha_lower
  have hup := (aux_thm_prop_affine_parameters d hd).alpha_upper
  change (1 / 2 : ℝ) < (aux_thm_prop_affine_parameters d hd).alpha ∧ _
  dsimp only [aux_thm_prop_alpha]
  exact ⟨by linarith, hup, by linarith, by linarith⟩

end
end Paper


namespace Paper

/-- The single dimension-dependent choice supplies all three affine exponents
and the strict exponent inequality used in proportionality. -/
theorem thm_prop_affine_parameters (d : ℕ) (hd : 2 ≤ d) :
    (127 / 128 : ℝ) < aux_thm_prop_alpha d hd ∧
    aux_thm_prop_alpha d hd < 1 ∧
    0 < (aux_thm_prop_affine_parameters d hd).gamma ∧
    (aux_thm_prop_affine_parameters d hd).gamma < 1 ∧
    0 < (aux_thm_prop_affine_parameters d hd).zeta ∧
    affineExponent d (aux_thm_prop_alpha d hd) (127 / 128)
      (aux_thm_prop_affine_parameters d hd).gamma
      (aux_thm_prop_affine_parameters d hd).zeta < 0 := by
  exact ⟨(aux_thm_prop_affine_parameters d hd).alpha_lower,
    (aux_thm_prop_affine_parameters d hd).alpha_upper,
    (aux_thm_prop_affine_parameters d hd).gamma_lower,
    (aux_thm_prop_affine_parameters d hd).gamma_upper,
    (aux_thm_prop_affine_parameters d hd).zeta_pos,
    (aux_thm_prop_affine_parameters d hd).exponent_neg⟩

end Paper

