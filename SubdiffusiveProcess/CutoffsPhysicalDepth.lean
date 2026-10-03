module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Physical depth of a triadic collar cell

A subdivision level is relative to the root side. The physical ultraviolet
comparison uses the absolute triadic exponent of each cell.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- The absolute triadic exponent of an odd-grid cell. -/
theorem aux_cutoffs_physical_side (κ : ℤ) (J : ℕ) (R rho : ℝ)
    (hR : R = (3 : ℝ) ^ κ) (hrho : rho = R / (3 : ℝ) ^ J) :
    rho = (3 : ℝ) ^ (κ - (J : ℤ)) := by
  rw [hrho, hR, ← zpow_natCast, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]

/-- A nonpositive absolute exponent is a natural physical depth. -/
theorem aux_cutoffs_physical_depth (κ : ℤ) (J k_phys : ℕ) (rho : ℝ)
    (hrho : rho = (3 : ℝ) ^ (κ - (J : ℤ)))
    (hdepth : κ - (J : ℤ) = -(k_phys : ℤ)) :
    rho = (3 : ℝ) ^ (-(k_phys : ℝ)) := by
  rw [hrho, hdepth, ← Real.rpow_intCast]
  congr 1
  push_cast
  rfl

/-- The physical grid scale is above the ultraviolet threshold. -/
theorem aux_cutoffs_physical_above (N k_phys : ℕ) (rho : ℝ)
    (hrho : rho = (3 : ℝ) ^ (-(k_phys : ℝ)))
    (h : k_phys ≤ N) :
    (3 : ℝ) ^ (-(N : ℝ)) ≤ rho := by
  rw [hrho]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
  have hreal : (k_phys : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
  linarith

/-- The physical grid scale is below the ultraviolet threshold. -/
theorem aux_cutoffs_physical_below (N k_phys : ℕ) (rho : ℝ)
    (hrho : rho = (3 : ℝ) ^ (-(k_phys : ℝ)))
    (h : N < k_phys) :
    rho < (3 : ℝ) ^ (-(N : ℝ)) := by
  rw [hrho]
  apply (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).2
  have hreal : (N : ℝ) < (k_phys : ℝ) := by exact_mod_cast h
  linarith

/-- The scale factor used in the direct, below-wavelength energy bound. -/
theorem aux_cutoffs_physical_below_factor (N k_phys : ℕ) (rho eta : ℝ)
    (hrho : rho = (3 : ℝ) ^ (-(k_phys : ℝ)))
    (heta : 0 ≤ eta) (h : N < k_phys) :
    (3 : ℝ) ^ ((N : ℝ) * eta) ≤ rho ^ (-eta) := by
  have hle : (N : ℝ) * eta ≤ (k_phys : ℝ) * eta := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt h) heta
  calc
    (3 : ℝ) ^ ((N : ℝ) * eta) ≤ (3 : ℝ) ^ ((k_phys : ℝ) * eta) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hle
    _ = rho ^ (-eta) := by
      rw [hrho, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring

/-- A positive absolute exponent gives a superunit cell side. -/
theorem aux_cutoffs_physical_coarse (κ : ℤ) (J : ℕ) (rho : ℝ)
    (hrho : rho = (3 : ℝ) ^ (κ - (J : ℤ)))
    (hcoarse : 0 < κ - (J : ℤ)) : 1 < rho := by
  rw [hrho, ← Real.rpow_intCast]
  have hcast : (0 : ℝ) < ((κ - (J : ℤ)) : ℝ) := by
    exact_mod_cast hcoarse
  simpa using
    (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).2 hcast

/-- Direct coefficient maxima absorb into the below-wavelength cell energy. -/
theorem aux_cutoffs_physical_below_energy (d N k_phys : ℕ)
    (rho eta K M : ℝ) (hrho : rho = (3 : ℝ) ^ (-(k_phys : ℝ)))
    (heta : 0 ≤ eta) (hK : 0 ≤ K) (h : N < k_phys)
    (hM : M ≤ K * (3 : ℝ) ^ ((N : ℝ) * eta)) :
    M * rho ^ ((d : ℝ) - 2) ≤ K * rho ^ ((d : ℝ) - 2 - eta) := by
  have hscale := aux_cutoffs_physical_below_factor N k_phys rho eta hrho heta h
  have hrho_pos : 0 < rho := by rw [hrho]; positivity
  have hpow_nonneg : 0 ≤ rho ^ ((d : ℝ) - 2) :=
    Real.rpow_nonneg hrho_pos.le _
  calc
    M * rho ^ ((d : ℝ) - 2) ≤
        (K * (3 : ℝ) ^ ((N : ℝ) * eta)) * rho ^ ((d : ℝ) - 2) :=
      mul_le_mul_of_nonneg_right hM hpow_nonneg
    _ = K * ((3 : ℝ) ^ ((N : ℝ) * eta) * rho ^ ((d : ℝ) - 2)) := by ring
    _ ≤ K * (rho ^ (-eta) * rho ^ ((d : ℝ) - 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hscale hpow_nonneg) hK
    _ = K * rho ^ ((d : ℝ) - 2 - eta) := by
      rw [← Real.rpow_add hrho_pos]
      congr 1
      ring

end Paper







