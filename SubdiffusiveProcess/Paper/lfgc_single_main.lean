import SubdiffusiveProcess.Paper.lfgc_single_num2

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# The single-point tests have interval witnesses

For the roots of lem_band's parametrisation (levels `k + offset i`, `-3 ≤ offset i ≤ 0`) and
tolerance `θ₀ ≤ 1/8`: for every rate `R > 0` there is a disorder threshold such that, for every
model below it, every carrier of full measure on which the infrared partial sums converge and
the canonical sample has the canonical formula, and every `m, k, z`, the failure of the
near-unit property for the infrared field or for the zero field is covered by events measurable
in the layer windows `[-k-2h, -k+h]` with probabilities at most `e^{-R h}/2`.
-/

open MeasureTheory Filter Topology SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Disorder smallness that makes a positive quantity `C δ^c` at most `τ`. -/
theorem lfgc_single_main {C c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → C * δ ^ c ≤ τ := by
  set C' := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(τ / C') ^ (1 / c), by positivity, fun δ hδ hle => ?_⟩
  have h1 : δ ^ c ≤ ((τ / C') ^ (1 / c)) ^ c := Real.rpow_le_rpow hδ.le hle hc.le
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hc.ne', Real.rpow_one] at h1
  have h2 : C * δ ^ c ≤ C' * δ ^ c :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  calc C * δ ^ c ≤ C' * δ ^ c := h2
    _ ≤ C' * (τ / C') := mul_le_mul_of_nonneg_left h1 hC'.le
    _ = τ := by field_simp

end Paper
namespace Paper
theorem aux_lfgc_single_main_Kp_of_small {Cδ ρ E p τ : ℝ} (hρ1 : ρ < 1) (hE : 0 < E) (hp : 0 < p)
    (hτ : τ = (1 - ρ) / 32 * E ^ (1 / p)) (hCδ : 0 ≤ Cδ) (h : Cδ ≤ τ) :
    (32 * Cδ / (1 - ρ)) ^ p ≤ E := by
  have hden : 0 < 1 - ρ := by linarith
  have h2 : 32 * Cδ / (1 - ρ) ≤ E ^ (1 / p) := by
    rw [div_le_iff₀ hden]
    rw [hτ] at h
    have := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 32 by norm_num)
    linarith
  calc (32 * Cδ / (1 - ρ)) ^ p ≤ (E ^ (1 / p)) ^ p :=
        Real.rpow_le_rpow (by positivity) h2 hp.le
    _ = E := by rw [← Real.rpow_mul hE.le, one_div_mul_cancel hp.ne', Real.rpow_one]

theorem aux_lfgc_single_main_base_of_small {card p E s B τ' : ℝ} (hcard : 0 ≤ card) (hp : 0 < p) (hE : 0 < E)
    (hs : 0 < s) (hB : 0 ≤ B) (hτ' : τ' = s ^ 2 * (E / (card + 1)) ^ (1 / p)) (h : B ≤ τ') :
    card * (B / s ^ 2) ^ p ≤ E := by
  have hr : B / s ^ 2 ≤ (E / (card + 1)) ^ (1 / p) := by
    rw [div_le_iff₀ (by positivity)]; rw [hτ'] at h; linarith
  have hr2 : (B / s ^ 2) ^ p ≤ E / (card + 1) := by
    calc (B / s ^ 2) ^ p ≤ ((E / (card + 1)) ^ (1 / p)) ^ p :=
          Real.rpow_le_rpow (by positivity) hr hp.le
      _ = E / (card + 1) := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp.ne', Real.rpow_one]
  calc card * (B / s ^ 2) ^ p ≤ card * (E / (card + 1)) := mul_le_mul_of_nonneg_left hr2 hcard
    _ ≤ E := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

end Paper
