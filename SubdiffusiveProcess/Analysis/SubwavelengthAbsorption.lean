import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! An exponent gap absorbs a subgeometric cutoff constant below its wavelength. -/
namespace SubdiffusiveProcess

/-- Below the last wavelength an exponent gap cancels the corresponding exponential growth. -/
theorem subwavelength_rpow_absorb (K B e r : ℝ) (N : ℕ)
    (hB : 0 ≤ B) (he : 0 ≤ e) (hr : 0 < r) (hrN : r ≤ (3 : ℝ) ^ (-(N : ℤ)))
    (hK : K ≤ B * (3 : ℝ) ^ (e * (N : ℝ))) : K * r ^ e ≤ B := by
  have hp : (r ^ e) ≤ (3 : ℝ) ^ (-((N : ℝ) * e)) := by
    have hx := Real.rpow_le_rpow hr.le hrN he
    rw [← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)] at hx
    simpa only [neg_mul] using hx
  calc K * r ^ e ≤ (B * (3 : ℝ) ^ (e * (N : ℝ))) * r ^ e :=
      mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hr.le _)
    _ ≤ (B * (3 : ℝ) ^ (e * (N : ℝ))) * (3 : ℝ) ^ (-((N : ℝ) * e)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = B := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        show e * (N : ℝ) + -((N : ℝ) * e) = 0 by ring, Real.rpow_zero, mul_one]

/-- A stronger power estimate and its cutoff envelope imply the weaker uniform estimate. -/
theorem subwavelength_energy_absorb (E K B c t t0 r : ℝ) (N : ℕ)
    (hB : 0 ≤ B) (ht : t ≤ t0) (hr : 0 < r) (hrN : r ≤ (3 : ℝ) ^ (-(N : ℤ)))
    (hK : K ≤ B * (3 : ℝ) ^ ((t0 - t) * (N : ℝ)))
    (hE : E ≤ K * c ^ 2 * r ^ t0) : E ≤ B * c ^ 2 * r ^ t := by
  have h := subwavelength_rpow_absorb K B (t0 - t) r N hB (sub_nonneg.mpr ht) hr hrN hK
  have heq : K * c ^ 2 * r ^ t0 = (K * r ^ (t0 - t)) * (c ^ 2 * r ^ t) := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hr, sub_add_cancel]
  exact hE.trans (heq.le.trans ((mul_le_mul_of_nonneg_right h (by positivity)).trans_eq (by ring)))

end SubdiffusiveProcess
