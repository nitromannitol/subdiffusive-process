module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- An integer-power majorant replaces the fractional root of the spatial average. -/
theorem mass_power_majorant {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    t ≤ 1 + t ^ n := by
  by_cases h : t ≤ 1
  · exact h.trans (le_add_of_nonneg_right (pow_nonneg ht _))
  · exact (le_self_pow₀ (le_of_not_ge h) hn.ne').trans (by linarith)

theorem mass_half_power {d : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    (r ^ (1 / 2 : ℝ)) ^ (2 * d) = r ^ d := by
  rw [← Real.rpow_mul_natCast hr, ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem mass_small_scaling {d : ℕ} {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    s ^ d * (r / s) ^ ((d : ℝ) - 1 / 2) =
      s ^ (1 / 2 : ℝ) * r ^ ((d : ℝ) - 1 / 2) := by
  rw [Real.div_rpow hr.le hs.le, div_eq_mul_inv]
  rw [← Real.rpow_neg hs.le, ← Real.rpow_natCast, ← mul_assoc,
    mul_comm (s ^ (d : ℝ)) (r ^ ((d : ℝ) - 1 / 2)), mul_assoc,
    ← Real.rpow_add hs]
  have he : (d : ℝ) + -((d : ℝ) - 1 / 2) = 1 / 2 := by ring
  rw [he]
  ring

theorem mass_scaled_majorant {d : ℕ} (hd : 0 < d) {r a : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) :
    a ≤ r ^ (-1 / 2 : ℝ) + r ^ ((d : ℝ) - 1 / 2) * a ^ (2 * d) := by
  have h := mass_power_majorant (by omega : 0 < 2 * d)
    (mul_nonneg (Real.rpow_nonneg hr.le (1 / 2 : ℝ)) ha)
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hr.le (-1 / 2 : ℝ))
  have hid : r ^ (-1 / 2 : ℝ) * (r ^ (1 / 2 : ℝ) * a) = a := by
    rw [← mul_assoc, ← Real.rpow_add hr]
    norm_num
  have hid' : r ^ (-1 / 2 : ℝ) *
      (1 + (r ^ (1 / 2 : ℝ) * a) ^ (2 * d)) =
        r ^ (-1 / 2 : ℝ) + r ^ ((d : ℝ) - 1 / 2) * a ^ (2 * d) := by
    rw [mul_add, mul_one, mul_pow, mass_half_power hr.le, ← mul_assoc,
      ← Real.rpow_natCast r d, ← Real.rpow_add hr]
    congr 2
    ring
  rwa [hid, hid'] at hm

theorem mass_small_majorant {d : ℕ} (hd : 0 < d) {s a S : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hS : s ^ d * a ^ (2 * d) ≤ S) :
    s ^ (1 / 2 : ℝ) * a ≤ 1 + S := by
  have h := mass_power_majorant (by omega : 0 < 2 * d)
    (mul_nonneg (Real.rpow_nonneg hs.le (1 / 2 : ℝ)) ha)
  rw [mul_pow, mass_half_power hs.le] at h
  linarith

theorem mass_rpow_sum_bound {ι : Type*} (J : Finset ι) {w V Q : ℝ}
    (hw : 0 < w) (hV : w * (J.card : ℝ) ≤ V) (hQ : 1 ≤ Q)
    (a : ι → ℝ) (ha : ∀ j ∈ J, 0 ≤ a j) :
    (w * ∑ j ∈ J, a j) ^ Q ≤ V ^ (Q - 1) * (w * ∑ j ∈ J, a j ^ Q) := by
  have hsum := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg J hQ ha
  have hmul := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hw.le Q)
  rw [Real.mul_rpow hw.le (Finset.sum_nonneg ha)]
  refine hmul.trans ?_
  have heq : w ^ Q * (J.card : ℝ) ^ (Q - 1) =
      (w * (J.card : ℝ)) ^ (Q - 1) * w := by
    rw [Real.mul_rpow hw.le (Nat.cast_nonneg _), mul_assoc, mul_comm _ w,
      ← mul_assoc, ← Real.rpow_add_one hw.ne']
    congr 1
    ring
  rw [← mul_assoc, heq]
  calc
    ((w * (J.card : ℝ)) ^ (Q - 1) * w) * (∑ j ∈ J, a j ^ Q)
        ≤ (V ^ (Q - 1) * w) * (∑ j ∈ J, a j ^ Q) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (mul_nonneg hw.le (Nat.cast_nonneg _)) hV
            (sub_nonneg.mpr hQ)) hw.le)
        (Finset.sum_nonneg fun j hj => Real.rpow_nonneg (ha j hj) Q)
    _ = V ^ (Q - 1) * (w * ∑ j ∈ J, a j ^ Q) := by ring

theorem mass_one_add_rpow {S Q : ℝ} (hS : 0 ≤ S) (hQ : 1 ≤ Q) :
    (1 + S) ^ Q ≤ (2 : ℝ) ^ Q * (1 + S ^ Q) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (Finset.univ : Finset (Fin 2)) (f := fun i => if i = 0 then (1 : ℝ) else S) hQ
      (fun i _ => by split_ifs <;> positivity)
  simp [Fin.sum_univ_two] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)



end SubdiffusiveProcess.Section10
