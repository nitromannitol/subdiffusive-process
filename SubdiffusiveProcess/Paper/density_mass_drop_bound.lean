module

public import SubdiffusiveProcess.Paper.lem_finite_stopping_partition_tree
@[expose] public section

open Filter MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The logarithmic mass-drop bound used on each residual branch. The positive
floor is c times the volume at the observation depth; the intercept is fixed
before that depth and the branch are chosen. -/
theorem density_mass_drop_bound
    (L D dim A c : ℝ) (hL : 1 < L) (hD : 0 < D) (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (J : ℕ) (lam : ℕ → ℝ),
      (∀ n, lam (n + 1) ≤ lam n) → lam 0 ≤ A →
      c * L ^ (-dim * (J : ℝ)) ≤ lam J →
      (aux_lem_finite_stopping_partition_dropCount lam (L ^ D) J : ℝ) ≤
        (dim / D) * (J : ℝ) + B := by
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hden : 0 < D * Real.log L := mul_pos hD hlog
  let B := max 0 ((Real.log A - Real.log c) / (D * Real.log L))
  refine ⟨B, le_max_left _ _, ?_⟩
  intro J lam hmono hroot hfloor
  have hLD : 1 ≤ L ^ D := Real.one_le_rpow hL.le hD.le
  have hchain := aux_lem_finite_stopping_partition_mass_drop_chain lam (L ^ D) hLD hmono J
  have hmass : (L ^ D) ^ aux_lem_finite_stopping_partition_dropCount lam (L ^ D) J *
      (c * L ^ (-dim * (J : ℝ))) ≤ A :=
    ((mul_le_mul_of_nonneg_left hfloor (pow_nonneg (Real.rpow_nonneg hL0.le _) _)).trans hchain).trans hroot
  have hmasslog := Real.log_le_log (by positivity : 0 <
    (L ^ D) ^ aux_lem_finite_stopping_partition_dropCount lam (L ^ D) J *
      (c * L ^ (-dim * (J : ℝ)))) hmass
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow hL0, Real.log_mul hc.ne' (by positivity), Real.log_rpow hL0] at hmasslog
  have hraw : (aux_lem_finite_stopping_partition_dropCount lam (L ^ D) J : ℝ) ≤
      (dim / D) * (J : ℝ) + (Real.log A - Real.log c) / (D * Real.log L) := by
    apply (mul_le_mul_iff_right₀ hden).mp
    have heq : ((dim / D) * (J : ℝ) + (Real.log A - Real.log c) / (D * Real.log L)) *
        (D * Real.log L) = dim * (J : ℝ) * Real.log L + (Real.log A - Real.log c) := by
      field_simp [hD.ne', hlog.ne']
    nlinarith [heq]
  exact hraw.trans (add_le_add_right (le_max_right _ _) _)

end Paper
