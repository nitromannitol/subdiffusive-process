module

public import SubdiffusiveProcess.Static.HarmonicCutoffSmooth

@[expose] public section

/-! # The fixed gap exponent five and a comparable triadic mesh -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static
variable {d : ℕ}

theorem harmonic_cutoff_gap_five_bound {C0 g h B1 B2 Mc Kcut Crho rho0 : ℝ} (hC0 : 0 < C0) (hg : 0 < g) (hh : 0 < h)
    (h5 : 5 * h ≤ g) (hgr : g ≤ rho0 / 2) (hB1 : B1 = C0 / (g - 3 * h)) (hB2 : B2 = C0 / (g - 3 * h) ^ 2)
    (hMc : 0 ≤ Mc) (h3n : h⁻¹ ≤ Crho / g) (hCrho : 0 ≤ Crho)
    (hK : 8 ^ d * 25 * C0 ^ 2 * Crho * max 1 ((rho0 / 2) ^ 2) * (h * Mc) ≤ Kcut) :
    8 ^ d * (Mc * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 * h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2))) *
        h ^ (-(1 / 2 : ℝ)) ≤ Kcut * g ^ (-5 : ℝ) := by
  have hgh : 2 * g / 5 ≤ g - 3 * h := by linarith
  have hgh0 : 0 < g - 3 * h := by linarith
  have hexp : h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) * h ^ (-(1 / 2 : ℝ)) = (h ^ 2)⁻¹ := by
    rw [← Real.rpow_add hh]
    have : (d : ℝ) - 2 - ((d : ℝ) - 1 / 2) + -(1 / 2) = -2 := by ring
    rw [this, Real.rpow_neg hh.le]; norm_cast
  have hC : h * B1 / 2 + h * B1 + h ^ 2 * B2 ≤ h * (5 * C0 / g) := by
    rw [hB1, hB2]
    have e1 : C0 / (g - 3 * h) ≤ C0 / (2 * g / 5) := div_le_div_of_nonneg_left hC0.le (by positivity) hgh
    have e2 : C0 / (g - 3 * h) ^ 2 ≤ C0 / (2 * g / 5) ^ 2 :=
      div_le_div_of_nonneg_left hC0.le (by positivity) (pow_le_pow_left₀ (by positivity) hgh 2)
    have e3 : h * (C0 / (2 * g / 5) ^ 2) ≤ C0 / (2 * g / 5) * (1 / 2) := by
      have ea : C0 / (2 * g / 5) ^ 2 = 25 * C0 / (4 * g ^ 2) := by field_simp; ring
      have eb : C0 / (2 * g / 5) * (1 / 2) = 5 * C0 / (4 * g) := by field_simp; ring
      rw [ea, eb]
      have hh5 : h ≤ g / 5 := by linarith
      calc h * (25 * C0 / (4 * g ^ 2)) ≤ (g / 5) * (25 * C0 / (4 * g ^ 2)) := by gcongr
        _ = 5 * C0 / (4 * g) := by field_simp; ring
    calc h * (C0 / (g - 3 * h)) / 2 + h * (C0 / (g - 3 * h)) + h ^ 2 * (C0 / (g - 3 * h) ^ 2)
        ≤ h * (C0 / (2 * g / 5)) / 2 + h * (C0 / (2 * g / 5)) + h * (h * (C0 / (2 * g / 5) ^ 2)) := by
          rw [show h ^ 2 * (C0 / (g - 3 * h) ^ 2) = h * (h * (C0 / (g - 3 * h) ^ 2)) by ring]
          gcongr
      _ ≤ h * (C0 / (2 * g / 5)) / 2 + h * (C0 / (2 * g / 5)) + h * (C0 / (2 * g / 5) * (1 / 2)) := by
          gcongr
      _ = h * (5 * C0 / g) := by field_simp; ring
  have hg5 : g ^ (-5 : ℝ) = (g ^ 5)⁻¹ := by rw [Real.rpow_neg hg.le]; norm_cast
  rw [hg5, mul_assoc, show Mc * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 *
      h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) * h ^ (-(1 / 2 : ℝ)) =
      Mc * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 *
      (h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) * h ^ (-(1 / 2 : ℝ))) by ring, hexp]
  have hCsq : (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 ≤ (h * (5 * C0 / g)) ^ 2 := by
    have h0 : 0 ≤ h * B1 / 2 + h * B1 + h ^ 2 * B2 := by
      rw [hB1, hB2]; positivity
    exact pow_le_pow_left₀ h0 hC 2
  have hg2 : g ^ 2 ≤ max 1 ((rho0 / 2) ^ 2) :=
    le_max_of_le_right (pow_le_pow_left₀ hg.le hgr 2)
  have hinv : h⁻¹ * g ≤ Crho := by rwa [le_div_iff₀ hg] at h3n
  rw [le_mul_inv_iff₀ (by positivity)]
  calc 8 ^ d * (Mc * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 * (h ^ 2)⁻¹) * g ^ 5
      ≤ 8 ^ d * (Mc * (h * (5 * C0 / g)) ^ 2 * (h ^ 2)⁻¹) * g ^ 5 := by gcongr
    _ = 8 ^ d * 25 * C0 ^ 2 * (h⁻¹ * g) * g ^ 2 * (h * Mc) := by field_simp; ring
    _ ≤ 8 ^ d * 25 * C0 ^ 2 * Crho * max 1 ((rho0 / 2) ^ 2) * (h * Mc) := by gcongr
    _ ≤ Kcut := hK


theorem exists_harmonic_cutoff_mesh {g rho0 : ℝ} (hg : 0 < g) (hgr : g ≤ rho0 / 2) :
    ∃ n : ℕ, 1 ≤ n ∧ 5 * ((3 : ℝ) ^ n)⁻¹ ≤ g ∧ ((3 : ℝ) ^ n) ≤ (3 * rho0 / 2 + 15) / g ∧
      ∀ N : ℕ, N < n → (3 : ℝ) ^ N ≤ max 1 (5 / g) := by
  classical
  have hex : ∃ n : ℕ, 5 / g ≤ (3 : ℝ) ^ n :=
    (pow_unbounded_of_one_lt (5 / g) (by norm_num : (1 : ℝ) < 3)).imp fun n hn => hn.le
  set m := Nat.find hex with hm
  have hmspec : 5 / g ≤ (3 : ℝ) ^ m := Nat.find_spec hex
  have hmin : ∀ k < m, (3 : ℝ) ^ k < 5 / g := fun k hk => not_le.1 (Nat.find_min hex hk)
  refine ⟨max 1 m, le_max_left _ _, ?_, ?_, ?_⟩
  · have h1 : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ (max 1 m) := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    have h2 : 5 / g ≤ (3 : ℝ) ^ (max 1 m) := hmspec.trans h1
    rw [div_le_iff₀ hg] at h2
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  · rw [le_div_iff₀ hg]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, max_eq_left (by norm_num : (0 : ℕ) ≤ 1), pow_one]
      linarith
    · rw [max_eq_right hpos]
      have hprev := hmin (m - 1) (by omega)
      have hpow : (3 : ℝ) ^ m = 3 * (3 : ℝ) ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hpow]
      rw [lt_div_iff₀ hg] at hprev
      nlinarith
  · intro N hN
    by_cases hNm : N < m
    · exact (hmin N hNm).le.trans (le_max_right _ _)
    · have hm0 : m = 0 := by
        have : max 1 m = 1 ∨ max 1 m = m := by
          rcases le_total 1 m with h | h
          · right; exact max_eq_right h
          · left; exact max_eq_left h
        rcases this with h | h <;> omega
      have hN0 : N = 0 := by omega
      rw [hN0, pow_zero]
      exact le_max_left _ _


end SubdiffusiveProcess.Static
