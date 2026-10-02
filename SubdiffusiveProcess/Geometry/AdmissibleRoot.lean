import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set

namespace SubdiffusiveProcess

/-- Choose an actual half-triadic working radius with inactive-face clearance, an eightfold target separation, and the next-face bound when the radius is below the fixed root cap. -/
theorem exists_halfTriadic_admissible_root
    (m : ℤ) (L s δ : ℝ) (hL : 10 ≤ L) (hs : 0 < s)
    (hsmall : s < ((3 : ℝ) ^ m / 2) / 24)
    (hclear : 100 * L * s < δ) :
    ∃ k : ℤ, k ≤ m ∧
      8 * s < (3 : ℝ) ^ k / 2 ∧
      (3 : ℝ) ^ k / 2 ≤ (3 : ℝ) ^ m / 2 ∧
      4 * L * ((3 : ℝ) ^ k / 2) ≤ δ ∧
      (k < m → δ < 12 * L * ((3 : ℝ) ^ k / 2)) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hpowpos : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hscale_pos : 0 < (3 : ℝ) ^ m / 2 := div_pos hpowpos (by norm_num)
  have hdelta_pos : 0 < δ := by
    have hprod_pos : 0 < 100 * L * s := mul_pos (mul_pos (by norm_num) hLpos) hs
    exact hprod_pos.trans hclear
  have hdelta_scale_pos : 0 < δ / (4 * L) := div_pos hdelta_pos (mul_pos (by norm_num) hLpos)
  let cap : ℝ := min ((3 : ℝ) ^ m / 2) (δ / (4 * L))
  have hcap_pos : 0 < cap := by
    dsimp [cap]
    exact lt_min hscale_pos hdelta_scale_pos
  have htarget_pos : 0 < 2 * cap := mul_pos (by norm_num) hcap_pos
  obtain ⟨k, hklo, hkhi⟩ := exists_mem_Ico_zpow htarget_pos (show (1 : ℝ) < 3 by norm_num)
  have hnext : 2 * cap < 3 * (3 : ℝ) ^ k := by
    simpa [zpow_add₀, mul_comm] using hkhi
  have hRlecap : (3 : ℝ) ^ k / 2 ≤ cap := by linarith
  have hcap_lt_threeR : cap < 3 * ((3 : ℝ) ^ k / 2) := by linarith
  have hcap_le_scale : cap ≤ (3 : ℝ) ^ m / 2 := min_le_left _ _
  have hcap_le_delta : cap ≤ δ / (4 * L) := min_le_right _ _
  have hRle_scale : (3 : ℝ) ^ k / 2 ≤ (3 : ℝ) ^ m / 2 := hRlecap.trans hcap_le_scale
  have hkpow_le : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m := by linarith
  have hkm : k ≤ m := (zpow_le_zpow_iff_right₀ (show (1 : ℝ) < 3 by norm_num)).mp hkpow_le
  have hdelta_large : 25 * s < δ / (4 * L) := by
    rw [lt_div_iff₀ (mul_pos (by norm_num) hLpos)]
    nlinarith
  have hscale_large : 24 * s < (3 : ℝ) ^ m / 2 := by nlinarith [hsmall]
  have hcap_large : 24 * s < cap := by
    rw [lt_min_iff]
    constructor
    · exact hscale_large
    · linarith
  have hratio : 8 * s < (3 : ℝ) ^ k / 2 := by linarith
  have hclearR : 4 * L * ((3 : ℝ) ^ k / 2) ≤ δ := by
    have hden_pos : 0 < 4 * L := mul_pos (by norm_num) hLpos
    have := mul_le_mul_of_nonneg_left hRlecap (le_of_lt hden_pos)
    calc
      4 * L * ((3 : ℝ) ^ k / 2) ≤ 4 * L * cap := by simpa [mul_assoc] using this
      _ ≤ δ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (le_div_iff₀ hden_pos).mp hcap_le_delta
  refine ⟨k, hkm, hratio, hRle_scale, hclearR, ?_⟩
  intro hkm_strict
  have hk1_le_m : k + 1 ≤ m := by omega
  have hnext_pow_le_m : (3 : ℝ) ^ (k + 1) ≤ (3 : ℝ) ^ m :=
    (zpow_le_zpow_iff_right₀ (show (1 : ℝ) < 3 by norm_num)).2 hk1_le_m
  have hthreeR_le_scale : 3 * ((3 : ℝ) ^ k / 2) ≤ (3 : ℝ) ^ m / 2 := by
    have hpow_succ : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by
      rw [zpow_add₀]
      · ring
      · norm_num
    rw [hpow_succ] at hnext_pow_le_m
    linarith
  have hdelta_le_scale : δ / (4 * L) ≤ (3 : ℝ) ^ m / 2 := by
    by_contra hnot
    have hscale_lt_delta : (3 : ℝ) ^ m / 2 < δ / (4 * L) := lt_of_not_ge hnot
    have hcap_eq_scale : cap = (3 : ℝ) ^ m / 2 := by
      exact min_eq_left (le_of_lt hscale_lt_delta)
    rw [hcap_eq_scale] at hcap_lt_threeR
    exact (not_lt_of_ge hthreeR_le_scale) hcap_lt_threeR
  have hcap_eq_delta : cap = δ / (4 * L) := min_eq_right hdelta_le_scale
  rw [hcap_eq_delta] at hcap_lt_threeR
  have hden_pos : 0 < 4 * L := mul_pos (by norm_num) hLpos
  apply (div_lt_iff₀ hden_pos).mp at hcap_lt_threeR
  nlinarith

end SubdiffusiveProcess
