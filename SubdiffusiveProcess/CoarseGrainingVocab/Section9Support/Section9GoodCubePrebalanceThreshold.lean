module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedPrebalance
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section

/-!
# A fixed response tolerance for the Dirichlet prebalance estimate

Choose the intermediate depth and response tolerance after the desired
error, before the disorder, model, or moment exponent.
-/

set_option autoImplicit false
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Small responses at a fixed depth make the normalized prebalance core small. -/
theorem goodCube_exists_fixed_prebalance_threshold
    (s1 s2 C eps : ℝ) (hs2 : 0 < s2) (hC : 0 < C) (heps : 0 < eps) :
    ∃ (k : ℕ) (zeta : ℝ), 0 < k ∧ 0 < zeta ∧ zeta ≤ 1 ∧
      ∀ E1 E2 : ℝ, 0 ≤ E1 → 0 ≤ E2 → E1 ≤ zeta → E2 ≤ zeta →
        C * dirichletPrebalanceCore s1 s2 k E1 E2 (1 + 2 * E2) ≤ eps := by
  set rho := Real.rpow 3 (-s2) with hrhoeq
  have hrho0 : 0 < rho := by
    rw [hrhoeq]; exact Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) _
  have hrho1 : rho < 1 := by
    rw [hrhoeq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 3) (by linarith)
  have hrho_le1 : rho ≤ 1 := le_of_lt hrho1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos heps (mul_pos (by norm_num : (0:ℝ) < 4) hC)) hrho1
  have hrpow : rho ^ (n + 1) ≤ rho ^ n := by
    rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hrho0.le n) hrho_le1
  have hap : 0 < Real.rpow 3 (s1 * ((n + 1 : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) _
  have hzeta0 : 0 < min 1 (min (Real.rpow 3 (s1 * ((n + 1 : ℕ) : ℝ)))⁻¹
      (eps / (6 * C * Real.rpow 3 (s1 * ((n + 1 : ℕ) : ℝ))))) :=
    lt_min zero_lt_one (lt_min (inv_pos.mpr hap)
      (div_pos heps (mul_pos (mul_pos (by norm_num : (0:ℝ) < 6) hC) hap)))
  refine ⟨n + 1, min 1 (min (Real.rpow 3 (s1 * ((n + 1 : ℕ) : ℝ)))⁻¹
      (eps / (6 * C * Real.rpow 3 (s1 * ((n + 1 : ℕ) : ℝ))))),
    Nat.succ_pos n, hzeta0, min_le_left _ _, ?_⟩
  intro E1 E2 hE1 hE2 hE1z hE2z
  simp only [dirichletPrebalanceCore]
  set a := Real.rpow 3 (s1 * ((n + 1 : ℕ) : ℝ)) with haeq
  set b := Real.rpow 3 (-s2 * ((n + 1 : ℕ) : ℝ)) with hbeq
  have hb0 : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hbp : b = rho ^ (n + 1) := by
    calc b = (3 : ℝ) ^ ((-s2) * ((n + 1 : ℕ) : ℝ)) := rfl
      _ = ((3 : ℝ) ^ (-s2)) ^ ((n + 1 : ℕ) : ℝ) :=
        Real.rpow_mul (by norm_num) _ _
      _ = rho ^ (n + 1) := by rw [Real.rpow_natCast]; rfl
  have hb_lt : b < eps / (4 * C) := by
    rw [hbp]
    exact lt_of_le_of_lt hrpow hn
  have hzeta_a : min 1 (min a⁻¹ (eps / (6 * C * a))) ≤ a⁻¹ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hzeta_e : min 1 (min a⁻¹ (eps / (6 * C * a))) ≤ eps / (6 * C * a) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hE2le1 : E2 ≤ 1 := le_trans hE2z (min_le_left _ _)
  have hY : 1 + 2 * E2 ≤ 3 := by linarith
  have hE2sq : E2 ^ (2:ℕ) ≤ E2 := by
    have h1 : E2 ^ (2:ℕ) = E2 * E2 := pow_two E2
    have h2 : E2 * E2 ≤ 1 * E2 := mul_le_mul_of_nonneg_right hE2le1 hE2
    rw [one_mul] at h2
    linarith
  have haE2 : a * E2 ≤ 1 := by
    have h1 : a * E2 ≤ a * a⁻¹ :=
      (mul_le_mul_of_nonneg_left hE2z hap.le).trans (mul_le_mul_of_nonneg_left hzeta_a hap.le)
    rwa [mul_inv_cancel₀ hap.ne'] at h1
  have haE2sq : a * E2 ^ (2:ℕ) ≤ 1 := by
    have h1 : a * E2 ^ (2:ℕ) ≤ a * E2 := mul_le_mul_of_nonneg_left hE2sq hap.le
    linarith
  have h1a : a * E1 ≤ eps / (6 * C) := by
    calc a * E1 ≤ a * (eps / (6 * C * a)) :=
          (mul_le_mul_of_nonneg_left hE1z hap.le).trans (mul_le_mul_of_nonneg_left hzeta_e hap.le)
      _ = eps / (6 * C) := by field_simp [hap.ne', hC.ne']
  have hle : C * (a * E1) ≤ eps / 6 := by
    calc C * (a * E1) ≤ C * (eps / (6 * C)) := mul_le_mul_of_nonneg_left h1a hC.le
      _ = eps / 6 := by field_simp [hC.ne']
  have h6 : 0 < eps / 6 := div_pos heps (by norm_num : (0:ℝ) < 6)
  have h1b : C * (a * E1 * (1 + 2 * E2)) ≤ eps / 2 := by
    have hnn : 0 ≤ C * (a * E1) := mul_nonneg hC.le (mul_nonneg hap.le hE1)
    calc C * (a * E1 * (1 + 2 * E2)) = (C * (a * E1)) * (1 + 2 * E2) := by ring
      _ ≤ (eps / 6) * 3 := mul_le_mul hle hY (by positivity) h6.le
      _ ≤ eps / 2 := by linarith
  have hble : C * b ≤ eps / 4 := by
    calc C * b ≤ C * (eps / (4 * C)) := mul_le_mul_of_nonneg_left (le_of_lt hb_lt) hC.le
      _ = eps / 4 := by field_simp [hC.ne']
  have hub : 1 + a * E2 ^ (2:ℕ) ≤ 2 := by linarith
  have h4 : 0 < eps / 4 := div_pos heps (by norm_num : (0:ℝ) < 4)
  have h2b : C * (b * (1 + a * E2 ^ (2:ℕ))) ≤ eps / 2 := by
    have hbnn : 0 ≤ C * b := mul_nonneg hC.le hb0.le
    calc C * (b * (1 + a * E2 ^ (2:ℕ))) = (C * b) * (1 + a * E2 ^ (2:ℕ)) := by ring
      _ ≤ (eps / 4) * 2 := mul_le_mul hble hub (by positivity) h4.le
      _ ≤ eps / 2 := by linarith
  have hsplit : C * (a * E1 * (1 + 2 * E2) + b * (1 + a * E2 ^ (2:ℕ))) =
      C * (a * E1 * (1 + 2 * E2)) + C * (b * (1 + a * E2 ^ (2:ℕ))) := by ring
  rw [hsplit]
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
