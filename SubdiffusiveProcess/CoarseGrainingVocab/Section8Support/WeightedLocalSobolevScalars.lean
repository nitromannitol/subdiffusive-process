module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyStepArithmetic
public import Mathlib
@[expose] public section

set_option autoImplicit false

/-! Exponent and scalar estimates for the weighted local Sobolev inequality. -/
open scoped ENNReal
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
theorem weightedSobolev_p0_gt_two {D : ℝ} (hD : 2 ≤ D) :
    2 < (2 + 1 / (2 * (4 * D - 3))) := by
  have hden : 0 < 2 * (4 * D - 3) := by nlinarith
  have hrecip : 0 < 1 / (2 * (4 * D - 3)) := by positivity
  linarith

theorem weightedSobolev_p0_le {D : ℝ} (hD : 2 ≤ D) :
    (2 + 1 / (2 * (4 * D - 3))) ≤ 21 / 10 := by
  have h1 : 0 < 4 * D - 3 := by linarith
  have h2 : 0 < 2 * (4 * D - 3) := by linarith
  field_simp
  nlinarith [hD]

theorem weightedSobolev_outer_pos {D : ℝ} (hD : 2 ≤ D) :
    0 < 2 / (2 + 1 / (2 * (4 * D - 3))) := by
  have h1 : 0 < 4 * D - 3 := by linarith
  have h2 : 0 < 2 * (4 * D - 3) := by linarith
  positivity

theorem weightedSobolev_outer_lt_one {D : ℝ} (hD : 2 ≤ D) :
    2 / (2 + 1 / (2 * (4 * D - 3))) < 1 := by
  have h1 : 0 < 4 * D - 3 := by linarith
  have h2 : 0 < 2 * (4 * D - 3) := by linarith
  have h3 : 0 < 2 + 1 / (2 * (4 * D - 3)) := by positivity
  field_simp
  nlinarith [h1]

theorem weightedSobolev_increment_exponent {D : ℝ} (hD : 2 ≤ D) :
    -(1 / 2 : ℝ) + D * (1 / 2 - 1 / (2 + 1 / (2 * (4 * D - 3)))) +
      3 / (8 * (2 + 1 / (2 * (4 * D - 3)))) ≤ -(1 / 4 : ℝ) := by
  have hden : (0 : ℝ) < 2 * (4 * D - 3) := by nlinarith
  set t := 1 / (2 * (4 * D - 3)) with ht
  have ht0 : (0 : ℝ) < t := by
    rw [ht]
    exact div_pos one_pos hden
  have htden : t * (2 * (4 * D - 3)) = 1 := by
    rw [ht]
    exact one_div_mul_cancel (ne_of_gt hden)
  have h2t : (0 : ℝ) < 2 + t := by nlinarith
  have hpos : (0 : ℝ) < 8 * (2 + t) := by nlinarith
  have hne2 : (2 + t : ℝ) ≠ 0 := ne_of_gt h2t
  have hne8 : (8 : ℝ) * (2 + t) ≠ 0 := ne_of_gt hpos
  have hD1 : (1 : ℝ) ≤ D := by nlinarith
  have hprod : (0 : ℝ) ≤ t * (D - 1) :=
    mul_nonneg (le_of_lt ht0) (by nlinarith)
  have hkey : t * (4 * D - 2) ≤ 1 := by
    have h6 : t * (4 * D - 2) ≤ t * (2 * (4 * D - 3)) := by nlinarith [hprod]
    rwa [htden] at h6
  have e3 : (-(1 / 2 : ℝ) + D * (1 / 2 - 1 / (2 + t)) + 3 / (8 * (2 + t))) * (8 * (2 + t)) =
      -5 - 4 * t + 4 * D * t := by
    field_simp [hne2, hne8]
    ring
  have e2 : (8 : ℝ) * (2 + t) * (-(1 / 4 : ℝ)) = -4 - 2 * t := by ring
  have main : (-(1 / 2 : ℝ) + D * (1 / 2 - 1 / (2 + t)) + 3 / (8 * (2 + t))) * (8 * (2 + t)) ≤
      (8 : ℝ) * (2 + t) * (-(1 / 4 : ℝ)) := by
    rw [e3, e2]
    nlinarith [hkey]
  exact (mul_le_mul_iff_right₀ hpos).mp (by
    simpa only [mul_comm] using main)

theorem weightedSobolev_p0_lt_three {D : ℝ} (hD : 2 ≤ D) :
    (2 + 1 / (2 * (4 * D - 3))) < 3 := by
  linarith [weightedSobolev_p0_le hD]

theorem weightedSobolev_interpolation_exponent_nonneg {D : ℝ} (hD : 2 ≤ D) :
    0 ≤ 1 / 2 - 1 / (2 + 1 / (2 * (4 * D - 3))) := by
  have hp := weightedSobolev_p0_gt_two hD
  have hp0 : 0 < 2 + 1 / (2 * (4 * D - 3)) := by linarith
  have hi := (inv_lt_inv₀ hp0 (by norm_num : (0:ℝ) < 2)).mpr hp
  simp only [one_div] at *
  linarith

theorem weightedSobolev_power_factor {x A p : ℝ} (hx : 0 ≤ x)
    (hA : x ≤ A) (hp : 2 ≤ p) : x ^ p ≤ A ^ (p - 2) * x ^ (2 : ℝ) := by
  by_cases hx0 : x = 0
  · subst x
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hsplit : x ^ p = x ^ (p - 2) * x ^ (2 : ℝ) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hA (sub_nonneg.mpr hp))
      (Real.rpow_nonneg hx 2)

theorem weightedSobolev_finset_square_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x : ι → ℝ) (i : ι) (hi : i ∈ S) :
    (x i) ^ 2 ≤ ∑ k ∈ S, (x k) ^ 2 := by
  exact Finset.single_le_sum (fun k _ => sq_nonneg (x k)) hi

theorem weightedSobolev_scaled_moment {a t M : ℝ≥0∞} {p : ℝ}
    (hp : 0 ≤ p) (h : a * t ≤ M) : a ^ p * t ^ p ≤ M ^ p := by
  have h1 := ENNReal.rpow_le_rpow h hp
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hp] using h1

theorem weightedSobolev_scale_cancel (m : ℝ) (j : ℕ) (D : ℝ) :
    (-(1 / 8 : ℝ) * m) * (4 * D) +
      ((m - (j : ℝ)) * (1 / 8)) * (4 * D) - D * (j : ℝ) =
      -(3 / 8 : ℝ) * (j : ℝ) * (4 * D) := by
  ring

theorem weightedSobolev_mass_root {x B : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B)
    {p : ℝ} (hp : 1 ≤ p) (h : x ^ p ≤ 8 * B ^ p) : x ≤ 8 * B := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h8 : (8:ℝ) ≤ 8 ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) hp
  have hBp : 0 ≤ B ^ p := Real.rpow_nonneg hB p
  have h2 : x ^ p ≤ 8 ^ p * B ^ p :=
    le_trans h (mul_le_mul_of_nonneg_right h8 hBp)
  have h3 : x ^ p ≤ (8 * B) ^ p := by
    calc x ^ p ≤ 8 ^ p * B ^ p := h2
      _ = (8 * B) ^ p := (Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) hB).symm
  exact (Real.rpow_le_rpow_iff hx (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hB) hp0).mp h3

theorem weightedSobolev_mass_shift {w K z : ℝ} (hz : 1 ≤ z)
    (_hK : 0 ≤ K) (h : |w - 1| ≤ K * z) : w ≤ (1 + K) * z := by
  nlinarith [le_abs_self (w - 1), h, hz]

theorem weightedSobolev_sum_increments (v : ℕ → ℝ) (N : ℕ) :
    v 0 + ∑ j ∈ Finset.range N, (v (j + 1) - v j) = v N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [ih]

theorem weightedSobolev_card_exponent (D : ℝ) (hD : 0 < D) (j : ℕ) :
    D * (j : ℝ) / (4 * D) + (j : ℝ) / 8 = (3 : ℝ) * (j : ℝ) / 8 := by
  field_simp
  ring

theorem weightedSobolev_rpow_cancel_scale (x : ℝ) (hx : 0 < x) (a b : ℝ) :
    x ^ a * x ^ (b - a) = x ^ b := by
  rw [← Real.rpow_add hx]; congr 1; ring

theorem weightedSobolev_positive_base_rpow {p : ℝ} (hp : 1 ≤ p) :
    (8 : ℝ) ≤ (8 : ℝ) ^ p := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) hp
  simpa using h

theorem weightedSobolev_increment_exponent_sum {D p : ℝ}
    (h : -(1 / 2 : ℝ) + D * (1 / 2 - 1 / p) + 3 / (8 * p) ≤ -(1 / 4 : ℝ))
    (j : ℕ) :
    (3 / 8 : ℝ) * ((j : ℝ) + 1) / p +
      (D * ((j : ℝ) + 1)) * (1 / 2 - 1 / p) - (j : ℝ) / 2 ≤
      (1 / 4 : ℝ) - (j : ℝ) / 4 := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy.weightedEnergy_step_exponent (D := D) (p := p) (h := h) (j := j)

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
