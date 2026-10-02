/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.Section9.BesovScaleHolder
import SubdiffusiveProcess.Section9.BesovPowerAlgebra

/-!
# Geometrically weighted sequence embedding

This file records the extended-valued scale embedding used by the Section 9
negative Besov comparison.
-/

namespace SubdiffusiveProcess.Section9

open scoped BigOperators ENNReal

/-- A geometrically weighted `ℓᵖ` norm is controlled by the unweighted
`ℓᴾ` norm.  The statement remains valid when either side is infinite. -/
theorem ennreal_geometric_weighted_lp_le_larger (rho : ENNReal) (a : ℕ → ENNReal)
    {p P : ℝ} (hp : 0 < p) (hpP : p < P) :
    (∑' j : ℕ, (rho ^ (j : ℕ) * a j) ^ p) ^ p⁻¹ ≤
      ((1 - rho ^ (p * P / (P - p)))⁻¹) ^ ((P - p) / (p * P)) *
        (∑' j : ℕ, (a j) ^ P) ^ P⁻¹ := by
  let r : ℝ := P / (P - p)
  let q : ℝ := P / p
  have hP : 0 < P := hp.trans hpP
  have hsub : 0 < P - p := sub_pos.mpr hpP
  have hr : 0 < r := div_pos hP hsub
  have hq : 0 < q := div_pos hP hp
  have hrq : r.HolderConjugate q := {
    inv_add_inv_eq_inv := by
      dsimp only [r, q]
      (field_simp [hp.ne', hP.ne', hsub.ne']; ring_nf)
    left_pos := hr
    right_pos := hq }
  have hterm : ∀ j : ℕ,
      (rho ^ (j : ℕ) * a j) ^ p = (rho ^ p) ^ (j : ℕ) * (a j) ^ p := by
    intro j
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring_nf
  have hholder := ennrealTsum_geometric_mul_le_Lp_mul_Lq
    (rho ^ p) (fun j ↦ (a j) ^ p) hrq
  rw [← tsum_congr hterm] at hholder
  have hroot := ENNReal.rpow_le_rpow hholder (inv_nonneg.mpr hp.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hroot
  have hrExp : p * r = p * P / (P - p) := by
    dsimp only [r]
    field_simp [hsub.ne']
  have hqExp : p * q = P := by
    dsimp only [q]
    field_simp [hp.ne']
  have hrInvPInv : r⁻¹ * p⁻¹ = (P - p) / (p * P) := by
    dsimp only [r]
    field_simp [hp.ne', hP.ne', hsub.ne']
  have hqInvPInv : q⁻¹ * p⁻¹ = P⁻¹ := by
    dsimp only [q]
    field_simp [hp.ne', hP.ne']
  have hsum : (∑' j : ℕ, ((a j) ^ p) ^ q) = ∑' j : ℕ, (a j) ^ P := by
    apply tsum_congr
    intro j
    rw [← ENNReal.rpow_mul, hqExp]
  rw [hrExp, hsum, hrInvPInv] at hroot
  rw [← ENNReal.rpow_mul, hqInvPInv] at hroot
  exact hroot

/-- For a subunit geometric ratio, the embedding factor is genuinely positive
and finite, including at `rho = 0`. -/
theorem ennreal_geometric_embedding_factor_pos_lt_top (rho : ENNReal)
    {p P : ℝ} (hrho : rho < 1) (hp : 0 < p) (hpP : p < P) :
    0 < ((1 - rho ^ (p * P / (P - p)))⁻¹) ^ ((P - p) / (p * P)) ∧
      ((1 - rho ^ (p * P / (P - p)))⁻¹) ^ ((P - p) / (p * P)) < ∞ := by
  have hP : 0 < P := hp.trans hpP
  have hsub : 0 < P - p := sub_pos.mpr hpP
  have ht : 0 < p * P / (P - p) := div_pos (mul_pos hp hP) hsub
  have he : 0 < (P - p) / (p * P) := div_pos hsub (mul_pos hp hP)
  have hrpow : rho ^ (p * P / (P - p)) < 1 :=
    ENNReal.rpow_lt_one hrho ht
  have hbasePos : 0 < 1 - rho ^ (p * P / (P - p)) :=
    tsub_pos_iff_lt.mpr hrpow
  have hbaseTop : 1 - rho ^ (p * P / (P - p)) ≠ ∞ := by
    exact ne_of_lt ((tsub_le_self : 1 - rho ^ (p * P / (P - p)) ≤ 1).trans_lt
      ENNReal.one_lt_top)
  have hinvPos : 0 < (1 - rho ^ (p * P / (P - p)))⁻¹ :=
    ENNReal.inv_pos.mpr hbaseTop
  have hinvTop : (1 - rho ^ (p * P / (P - p)))⁻¹ ≠ ∞ :=
    (ENNReal.inv_lt_top.mpr hbasePos).ne
  exact ⟨ENNReal.rpow_pos hinvPos hinvTop,
    ENNReal.rpow_lt_top_of_nonneg he.le hinvTop⟩

end SubdiffusiveProcess.Section9
