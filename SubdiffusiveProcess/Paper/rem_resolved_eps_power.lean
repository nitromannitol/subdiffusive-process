module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Paper.lem_load
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.lane4_smoothed_load_properties

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem rem_resolved_eps_power :
  ∀ (Eeps : ℝ → ℝ) (Gam : ℝ → ℝ → ℝ) (E0 KN Cmac Cmic t : ℝ),
    0 ≤ KN → 0 ≤ E0 → 0 ≤ Cmac → 0 ≤ Cmic →
    -- the load approximation of `\noderef{lem_load}` at the face-bump load: the right-hand
    -- side is free of `ε`, which is the point of the display at line 1127
    (∀ eps : ℝ, 0 < eps → eps < 1 / 8 → Eeps eps ≤ 2 * E0 + KN) →
    -- the two steps: the macroscopic one sees only the energy, through the Newtonian
    -- primitive; the microscopic one enters through `m_N⁻¹‖f_ε‖_∞² ≍ ε^{-2}`
    (∀ eps r : ℝ, 0 < eps → eps < 1 / 8 → 0 < r → r ≤ 1 →
      Gam eps r ≤ Cmac * Eeps eps * r ^ t + Cmic * (eps⁻¹ * eps⁻¹) * r ^ t) →
    -- hence `eq:mfd-13` with the explicit prefactor `(C_mac(2E_0+K)+C_mic) ε^{-2}`
    ∀ eps r : ℝ, 0 < eps → eps < 1 / 8 → 0 < r → r ≤ 1 →
      Gam eps r ≤ (Cmac * (2 * E0 + KN) + Cmic) * (eps⁻¹ * eps⁻¹) * r ^ t := by
  intro Eeps Gam E0 KN Cmac Cmic t hKN hE0 hCmac hCmic hload hsplit eps r heps heps8 hr hr1
  set K : ℝ := 2 * E0 + KN with hK
  set P : ℝ := eps⁻¹ * eps⁻¹ with hP
  set S : ℝ := r ^ t with hS
  have hSnn : (0 : ℝ) ≤ S := (Real.rpow_pos_of_pos hr t).le
  have hKnn : (0 : ℝ) ≤ K := by rw [hK]; linarith
  have hP1 : (1 : ℝ) ≤ P := by
    have h8 : eps < 1 := by linarith
    have hinv : (1 : ℝ) ≤ eps⁻¹ := (one_le_inv_iff₀).2 ⟨heps, h8.le⟩
    rw [hP]; nlinarith
  have hE : Eeps eps ≤ K := hload eps heps heps8
  -- the macroscopic term: the ε-free energy bound, absorbed using ε^{-2} ≥ 1
  have hA : Cmac * Eeps eps * S ≤ Cmac * K * (P * S) := by
    have t1 : Cmac * Eeps eps ≤ Cmac * K := mul_le_mul_of_nonneg_left hE hCmac
    have t3 : Cmac * Eeps eps * S ≤ Cmac * K * S := mul_le_mul_of_nonneg_right t1 hSnn
    have t4 : S ≤ P * S := by nlinarith
    have t5 : Cmac * K * S ≤ Cmac * K * (P * S) :=
      mul_le_mul_of_nonneg_left t4 (mul_nonneg hCmac hKnn)
    linarith
  have hsum := hsplit eps r heps heps8 hr hr1
  calc Gam eps r ≤ Cmac * Eeps eps * S + Cmic * P * S := hsum
    _ ≤ Cmac * K * (P * S) + Cmic * P * S := by linarith
    _ = (Cmac * K + Cmic) * P * S := by ring
    _ = (Cmac * (2 * E0 + KN) + Cmic) * (eps⁻¹ * eps⁻¹) * r ^ t := by rw [hK, hP, hS]

end Paper
