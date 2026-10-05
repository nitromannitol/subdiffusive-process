module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

/-! # A large ball between a small ball and a containing ball

If the closed ball `B̄(z, c/2)` lies in the open ball `B(p, P)` and `27 c ≤ 2 P`, then some ball
of radius `27 c / 2` contains `B̄(z, c/18)` and lies in `B(p, P)`.  The centre is moved from `z`
towards `p`.  This file asserts nothing beyond this metric fact. -/

open Metric

namespace SubdiffusiveProcess

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A closed ball inside an open ball leaves room: `‖z - p‖ + ρ < P`. -/
theorem norm_sub_add_lt_of_closedBall_subset_ball [Nontrivial E] {z p : E} {ρ P : ℝ}
    (hρ : 0 ≤ ρ) (h : closedBall z ρ ⊆ ball p P) : ‖z - p‖ + ρ < P := by
  by_cases hzp : z = p
  · obtain ⟨v, hv⟩ := exists_norm_eq E hρ
    have hmem : z + v ∈ closedBall z ρ := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hv]
    have := h hmem
    rw [mem_ball, dist_eq_norm, hzp, add_sub_cancel_left, hv] at this
    rw [hzp, sub_self, norm_zero, zero_add]
    exact this
  · have hD : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
    let e : E := ‖z - p‖⁻¹ • (z - p)
    have hmem : z + ρ • e ∈ closedBall z ρ := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul,
        norm_inv, norm_norm, inv_mul_cancel₀ hD.ne', mul_one, Real.norm_eq_abs, abs_of_nonneg hρ]
    have hin := h hmem
    rw [mem_ball, dist_eq_norm] at hin
    have heq : z + ρ • e - p = (1 + ρ * ‖z - p‖⁻¹) • (z - p) := by
      simp only [e, smul_smul, add_smul, one_smul]
      abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hin
    have hcalc : (1 + ρ * ‖z - p‖⁻¹) * ‖z - p‖ = ‖z - p‖ + ρ := by
      field_simp
    linarith only [hin, hcalc]

/-- Between `B̄(z, c/18)` and a ball `B(p, P)` containing `B̄(z, c/2)` there is a ball of radius
`27 c / 2`, provided `27 c ≤ 2 P`. -/
theorem exists_ball_between [Nontrivial E] {z p : E} {c P : ℝ} (hc : 0 < c)
    (hpad : closedBall z (c / 2) ⊆ ball p P) (hwide : 27 * c ≤ 2 * P) :
    ∃ w : E, closedBall z (c / 18) ⊆ ball w (27 * c / 2) ∧ ball w (27 * c / 2) ⊆ ball p P := by
  have hroom := norm_sub_add_lt_of_closedBall_subset_ball (by positivity) hpad
  set D : ℝ := ‖z - p‖ with hDdef
  by_cases hsmall : D ≤ 13 * c
  · refine ⟨p, ?_, ?_⟩
    · intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx
      rw [mem_ball, dist_eq_norm]
      have htri : ‖x - p‖ ≤ ‖x - z‖ + ‖z - p‖ := by
        have := norm_add_le (x - z) (z - p)
        rwa [sub_add_sub_cancel] at this
      linarith only [htri, hx, hsmall, hc]
    · exact ball_subset_ball (by linarith only [hwide])
  · push Not at hsmall
    have hD : 0 < D := by linarith only [hsmall, hc]
    let w : E := z + (13 * c / D) • (p - z)
    have hwz : ‖w - z‖ = 13 * c := by
      have : w - z = (13 * c / D) • (p - z) := by simp only [w, add_sub_cancel_left]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), norm_sub_rev, ← hDdef]
      field_simp
    have hwp : ‖w - p‖ = D - 13 * c := by
      have : w - p = (1 - 13 * c / D) • (z - p) := by
        simp only [w, sub_smul, one_smul, smul_sub]
        abel
      have hcoef : 0 ≤ 1 - 13 * c / D := by
        rw [sub_nonneg, div_le_one hD]; exact hsmall.le
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, ← hDdef]
      field_simp
    refine ⟨w, ?_, ?_⟩
    · intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx
      rw [mem_ball, dist_eq_norm]
      have htri : ‖x - w‖ ≤ ‖x - z‖ + ‖z - w‖ := by
        have := norm_add_le (x - z) (z - w)
        rwa [sub_add_sub_cancel] at this
      rw [norm_sub_rev z w, hwz] at htri
      linarith only [htri, hx, hc]
    · intro y hy
      rw [mem_ball, dist_eq_norm] at hy ⊢
      have htri : ‖y - p‖ ≤ ‖y - w‖ + ‖w - p‖ := by
        have := norm_add_le (y - w) (w - p)
        rwa [sub_add_sub_cancel] at this
      rw [hwp] at htri
      linarith only [htri, hy, hroom]

end SubdiffusiveProcess
