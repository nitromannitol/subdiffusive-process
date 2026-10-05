module

public import Mathlib

@[expose] public section

/-!
# Constants of the prefix cover

The moment order `p` of the prefix witness (large enough that `(3^{-a'/2})^p` beats the window
rate and that `p σ log 3/16 ≥ 2R`), the truncation offset `L0` (large enough that the uniform
truncation error is below the error scale), and the identity defining the error scale.
-/

namespace SubdiffusiveProcess.Lfgc
/-- Choice of the moment order. -/
theorem p1_moment_order {R a' sigma v : ℝ} (c1 : ℕ) (_hR : 0 < R) (ha' : 0 < a') (hs : 0 < sigma)
    (_hv : 0 ≤ v) :
    ∃ p : ℝ, 1 ≤ p ∧ ((3 : ℝ) ^ (-(a' / 2))) ^ p ≤ Real.exp (-(2 + v + R * c1)) ∧
      2 * R ≤ p * (sigma * Real.log 3 / 16) := by
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set p := max 1 (max ((2 + v + R * c1) / (a' / 2 * Real.log 3))
    (2 * R / (sigma * Real.log 3 / 16))) with hp
  have hp1 : 1 ≤ p := le_max_left _ _
  have hpa : (2 + v + R * c1) / (a' / 2 * Real.log 3) ≤ p := (le_max_left _ _).trans (le_max_right _ _)
  have hps : 2 * R / (sigma * Real.log 3 / 16) ≤ p := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨p, hp1, ?_, ?_⟩
  · rw [← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    refine Real.exp_le_exp.mpr ?_
    have hpos : 0 < a' / 2 * Real.log 3 := by positivity
    rw [div_le_iff₀ hpos] at hpa
    nlinarith
  · have hpos : 0 < sigma * Real.log 3 / 16 := by positivity
    rw [div_le_iff₀ hpos] at hps
    linarith

/-- Choice of the truncation offset. -/
theorem p1_offset {E κ R p sigma : ℝ} (hE : 0 ≤ E) (hκ : 0 < κ) (hR : 0 < R) (hp : 1 ≤ p)
    (_hs : 0 < sigma) (hps : 2 * R ≤ p * (sigma * Real.log 3 / 16)) :
    ∃ L0 : ℕ, E * (3 : ℝ) ^ (-(sigma / 16 * (L0 : ℝ))) ≤ κ * Real.exp (-(R * L0 / p)) := by
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hp0 : 0 < p := by linarith
  set α := sigma * Real.log 3 / 16 with hα
  set β := R / p with hβ
  have hβα : β < α := by
    rw [hβ, div_lt_iff₀ hp0]
    nlinarith
  obtain ⟨L0, hL0⟩ := exists_nat_gt (Real.log ((E + 1) / κ) / (α - β))
  refine ⟨L0, ?_⟩
  have h3 : (3 : ℝ) ^ (-(sigma / 16 * (L0 : ℝ))) = Real.exp (-(α * L0)) := by
    rw [Real.rpow_def_of_pos (by norm_num), hα]; congr 1; ring
  rw [h3, show -(R * L0 / p) = -(β * L0) by rw [hβ]; ring]
  have hab : 0 < α - β := by linarith
  have hkey : Real.log ((E + 1) / κ) ≤ (α - β) * L0 := by
    rw [div_lt_iff₀ hab] at hL0; linarith
  have hE1 : E + 1 ≤ κ * Real.exp ((α - β) * L0) := by
    have := Real.exp_le_exp.mpr hkey
    rw [Real.exp_log (by positivity)] at this
    rw [div_le_iff₀ hκ] at this
    linarith
  calc E * Real.exp (-(α * L0)) ≤ (E + 1) * Real.exp (-(α * L0)) := by
        gcongr; linarith
    _ ≤ κ * Real.exp ((α - β) * L0) * Real.exp (-(α * L0)) := by gcongr
    _ = κ * Real.exp (-(β * L0)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The error scale identity. -/
theorem p1_merr_identity {q K' Cg R p : ℝ} (hq : 0 < q) (hK' : 0 < K') (hCg : 0 ≤ Cg)
    (hp : 0 < p) (c : ℝ) :
    24 * (Cg + 1) * (2 * ((q * K' / 2) * (Real.exp (-(R * c)) / (24 * (Cg + 1))) ^ (1 / p)) /
      (q * K')) ^ p = Real.exp (-(R * c)) := by
  have h24 : 0 < 24 * (Cg + 1) := by positivity
  have hx : 2 * ((q * K' / 2) * (Real.exp (-(R * c)) / (24 * (Cg + 1))) ^ (1 / p)) / (q * K') =
      (Real.exp (-(R * c)) / (24 * (Cg + 1))) ^ (1 / p) := by
    field_simp
  rw [hx, ← Real.rpow_mul (by positivity), one_div_mul_cancel hp.ne', Real.rpow_one]
  field_simp

theorem p1_merr_split {q K' Cg R p : ℝ} (_hq : 0 < q) (_hK' : 0 < K') (hCg : 0 ≤ Cg) (_hp : 0 < p)
    (c L0 : ℝ) :
    (q * K' / 2) * (Real.exp (-(R * (c + L0))) / (24 * (Cg + 1))) ^ (1 / p) =
      ((q * K' / 2) * (Real.exp (-(R * c)) / (24 * (Cg + 1))) ^ (1 / p)) *
        Real.exp (-(R * L0 / p)) := by
  have h24 : 0 < 24 * (Cg + 1) := by positivity
  have hsplit : Real.exp (-(R * (c + L0))) / (24 * (Cg + 1)) =
      (Real.exp (-(R * c)) / (24 * (Cg + 1))) * Real.exp (-(R * L0)) := by
    rw [div_mul_eq_mul_div, ← Real.exp_add]; congr 2; ring
  rw [hsplit, Real.mul_rpow (by positivity) (by positivity)]
  have he : Real.exp (-(R * L0)) ^ (1 / p) = Real.exp (-(R * L0 / p)) := by
    rw [← Real.exp_mul]; congr 1; ring
  rw [he]
  ring

end SubdiffusiveProcess.Lfgc
