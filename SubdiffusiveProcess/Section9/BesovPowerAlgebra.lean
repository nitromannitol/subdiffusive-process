
module

public import Homogenization.Besov.Negative.ExactCirc

@[expose] public section

/-!
# Power normalization for the Section 9 Besov estimate

This file isolates the extended-nonnegative-real power algebra used when a
normalized child average is compared with a normalized parent average.
-/

namespace SubdiffusiveProcess.Section9

open scoped ENNReal

/-- The cardinality powers in a normalized spatial Hölder estimate collapse
to the parent-cardinality exponent.  No finiteness condition is imposed on the
payload `A`. -/
theorem normalized_holder_power_eq
    (n A : ℝ≥0∞) (p P : ℝ) (hn : n ≠ 0) (hntop : n ≠ ∞) (hp : 0 < p)
    (hP : 0 < P) :
    (n⁻¹ * (n ^ (1 - p / P) * A ^ (p / P))) ^ p⁻¹ =
      n ^ (-P⁻¹) * A ^ P⁻¹ := by
  have hpInv : 0 ≤ p⁻¹ := (inv_pos.mpr hp).le
  have hAexp : (p / P) * p⁻¹ = P⁻¹ := by
    field_simp [hp.ne', hP.ne']
  have hnexp : -1 * p⁻¹ + (1 - p / P) * p⁻¹ = -P⁻¹ := by
    field_simp [hp.ne', hP.ne']
    ring
  rw [← ENNReal.rpow_neg_one n, ENNReal.mul_rpow_of_nonneg _ _ hpInv,
    ENNReal.mul_rpow_of_nonneg _ _ hpInv, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc,
    ← ENNReal.rpow_add _ _ hn hntop,
    hnexp, hAexp]

/-- The same normalization identity expressed relative to a finite positive
parent cardinality `N`. -/
theorem normalized_holder_power_eq_parent
    (n N A : ℝ≥0∞) (p P : ℝ)
    (hn : n ≠ 0) (hntop : n ≠ ∞) (hN : N ≠ 0) (hNtop : N ≠ ∞)
    (hp : 0 < p) (hP : 0 < P) :
    (n⁻¹ * (n ^ (1 - p / P) * A ^ (p / P))) ^ p⁻¹ =
      (N / n) ^ P⁻¹ * (N⁻¹ * A) ^ P⁻¹ := by
  rw [normalized_holder_power_eq n A p P hn hntop hp hP]
  have hPInv : 0 ≤ P⁻¹ := (inv_pos.mpr hP).le
  have hneg : -P⁻¹ = -1 * P⁻¹ := by ring
  have hcancel : P⁻¹ + -1 * P⁻¹ = 0 := by ring
  rw [hneg]
  rw [div_eq_mul_inv, ← ENNReal.rpow_neg_one n, ← ENNReal.rpow_neg_one N,
    ENNReal.mul_rpow_of_nonneg _ _ hPInv,
    ENNReal.mul_rpow_of_nonneg _ _ hPInv, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  calc
    n ^ (-1 * P⁻¹) * A ^ P⁻¹ =
        (N ^ P⁻¹ * N ^ (-1 * P⁻¹)) *
          (n ^ (-1 * P⁻¹) * A ^ P⁻¹) := by
            rw [← ENNReal.rpow_add _ _ hN hNtop, hcancel,
              ENNReal.rpow_zero, one_mul]
    _ = (N ^ P⁻¹ * n ^ (-1 * P⁻¹)) *
          (N ^ (-1 * P⁻¹) * A ^ P⁻¹) := by ac_rfl

end SubdiffusiveProcess.Section9
