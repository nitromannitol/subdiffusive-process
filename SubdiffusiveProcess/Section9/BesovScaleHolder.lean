
module

public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-!
# Extended scale Hölder estimates

An extended-valued infinite-sum form of Hölder suitable for the exact Besov
scale aggregation.  Unlike the `NNReal` summability API, this remains valid
when either norm is infinite.
-/

namespace SubdiffusiveProcess.Section9

open scoped BigOperators ENNReal

/-- Hölder for `ENNReal` infinite sums, with no finiteness premise. -/
theorem ennrealTsum_mul_le_Lp_mul_Lq {ι : Type*} (f g : ι → ℝ≥0∞)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑' i, f i * g i ≤
      (∑' i, f i ^ p) ^ p⁻¹ * (∑' i, g i ^ q) ^ q⁻¹ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  refine (ENNReal.inner_le_Lp_mul_Lq S f g hpq).trans ?_
  apply mul_le_mul
  · simpa only [one_div] using
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum S) (inv_nonneg.mpr hpq.pos.le)
  · simpa only [one_div] using
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum S) (inv_nonneg.mpr hpq.symm.pos.le)
  · exact bot_le
  · exact bot_le

/-- The geometric weight occurring after scale Hölder has its exact extended
sum.  This statement deliberately does not totalize through real `toReal`. -/
theorem tsum_geometric_rpow (ρ : ℝ≥0∞) (t : ℝ) :
    ∑' j : ℕ, (ρ ^ (j : ℕ)) ^ t = (1 - ρ ^ t)⁻¹ := by
  rw [← ENNReal.tsum_geometric (ρ ^ t)]
  apply tsum_congr
  intro j
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  congr 1
  ring

/-- Infinite scale Hölder with the geometric factor evaluated explicitly.
This is the sequence-level form consumed after the exact-circ depth shift. -/
theorem ennrealTsum_geometric_mul_le_Lp_mul_Lq (ρ : ℝ≥0∞)
    (a : ℕ → ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑' j : ℕ, ρ ^ (j : ℕ) * a j ≤
      (1 - ρ ^ p)⁻¹ ^ p⁻¹ * (∑' j : ℕ, (a j) ^ q) ^ q⁻¹ := by
  calc
    ∑' j : ℕ, ρ ^ (j : ℕ) * a j ≤
        (∑' j : ℕ, (ρ ^ (j : ℕ)) ^ p) ^ p⁻¹ *
          (∑' j : ℕ, (a j) ^ q) ^ q⁻¹ :=
      ennrealTsum_mul_le_Lp_mul_Lq (fun j : ℕ => ρ ^ j) a hpq
    _ = (1 - ρ ^ p)⁻¹ ^ p⁻¹ * (∑' j : ℕ, (a j) ^ q) ^ q⁻¹ := by
      rw [tsum_geometric_rpow]

/-- Dropping a finite initial segment can only decrease an extended
nonnegative series. -/
theorem ennrealTsum_nat_add_le (a : ℕ) (b : ℕ → ℝ≥0∞) :
    ∑' j : ℕ, b (a + j) ≤ ∑' j : ℕ, b j := by
  exact ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_left_cancel h) b

/-- A finite positive constant factors exactly out of an extended `ℓ^p`
quantity. -/
theorem ennrealTsum_const_mul_rpow (c : ℝ≥0∞) (b : ℕ → ℝ≥0∞) (p : ℝ)
    (hp : 0 < p) :
    (∑' j : ℕ, (c * b j) ^ p) ^ p⁻¹ =
      c * (∑' j : ℕ, (b j) ^ p) ^ p⁻¹ := by
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (inv_pos.mpr hp).le,
    ← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]

end SubdiffusiveProcess.Section9
