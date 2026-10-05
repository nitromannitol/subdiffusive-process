module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.SmallScaleTail

@[expose] public section

namespace SubdiffusiveProcess.Besov
open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators ENNReal
noncomputable section

/-- The geometric tail has a uniform bound after multiplication by its order. -/
theorem discount_div_one_sub_le {t : ℝ} (ht : 0 < t) :
    (3 : ℝ) ^ (-t) / (1 - (3 : ℝ) ^ (-t)) ≤ 2 / t := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hexp := Real.add_one_le_exp (Real.log 3 * t)
  have hp : (3 : ℝ) ^ t = Real.exp (Real.log 3 * t) :=
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) t
  rw [← hp] at hexp
  have hlower : 1 + t / 2 ≤ (3 : ℝ) ^ t := by
    nlinarith [mul_le_mul_of_nonneg_right hlog ht.le]
  have hpos : 0 < (3 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) _
  have hgt : 1 < (3 : ℝ) ^ t := by linarith
  have hneg : (3 : ℝ) ^ (-t) = ((3 : ℝ) ^ t)⁻¹ := Real.rpow_neg (by norm_num) _
  rw [hneg]
  have hden : 0 < 1 - ((3 : ℝ) ^ t)⁻¹ := by
    have := (inv_lt_one₀ hpos).mpr hgt
    linarith
  apply (div_le_div_iff₀ hden ht).mpr
  have hc : (3 : ℝ) ^ t * ((3 : ℝ) ^ t)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hmul := mul_le_mul_of_nonneg_right hlower (inv_nonneg.mpr hpos.le)
  nlinarith

theorem sum_range_discount_shift_le {t : ℝ} (ht : 0 < t) (K N : ℕ) :
    (∑ i ∈ Finset.range N, ((3 : ℝ) ^ (-t)) ^ (K + 1 + i)) ≤
      (2 / t) * ((3 : ℝ) ^ (-t)) ^ K := by
  let ρ : ℝ := (3 : ℝ) ^ (-t)
  have hρ0 : 0 ≤ ρ := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hρ1 : ρ < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht)
  have hs : Summable fun i : ℕ => ρ ^ (K + 1 + i) := by
    exact ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (ρ ^ (K + 1))).congr
      (fun i => (pow_add ρ (K + 1) i).symm)
  calc
    (∑ i ∈ Finset.range N, ρ ^ (K + 1 + i)) ≤ ∑' i : ℕ, ρ ^ (K + 1 + i) :=
      hs.sum_le_tsum _ (fun i _ => pow_nonneg hρ0 _)
    _ = ρ ^ K * (ρ / (1 - ρ)) := by
      simp_rw [pow_add ρ (K + 1)]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1, pow_succ]
      ring
    _ ≤ ρ ^ K * (2 / t) :=
      mul_le_mul_of_nonneg_left (discount_div_one_sub_le ht) (pow_nonneg hρ0 _)
    _ = (2 / t) * ρ ^ K := mul_comm _ _

end
end SubdiffusiveProcess.Besov
