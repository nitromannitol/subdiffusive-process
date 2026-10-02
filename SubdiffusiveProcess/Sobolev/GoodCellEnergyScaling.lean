import SubdiffusiveProcess.Sobolev.CoarseEnergyArithmetic
import Mathlib.Tactic

/-!
# Good-cell energy scaling

This module proves two scalar consequences of normalized oscillation and trace-energy bounds. It does not establish either analytic input bound.
-/

open Real
namespace SubdiffusiveProcess

/-- A normalized quadratic oscillation bound gives the correctly scaled square-root estimate. -/
theorem oscillation_le_scaled_sqrt_of_sq_le
    (d : ℕ) (osc C r s nu : ℝ) (hC : 0 ≤ C) (hr : 0 < r) (hs : 0 < s) (hnu : 0 ≤ nu)
    (hbound : osc ^ 2 ≤ C ^ 2 * r ^ (2 - (d : ℝ)) * s⁻¹ * nu) :
    osc ≤ C * r ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt nu := by
  have hrpowSq : (r ^ ((2 - (d : ℝ)) / 2)) ^ 2 = r ^ (2 - (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    ring
  have hright : 0 ≤ C * r ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt nu :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hr.le _))
      (Real.rpow_nonneg hs.le _)) (Real.sqrt_nonneg _)
  have hhalfSq : (s ^ (-(1 : ℝ) / 2)) ^ 2 = s⁻¹ := by
    have hexp : (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) := by ring
    rw [hexp, rpow_neg_half_sq hs]
  have hrightSq :
      (C * r ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt nu) ^ 2 =
        C ^ 2 * r ^ (2 - (d : ℝ)) * s⁻¹ * nu := by
    rw [mul_pow, mul_pow, mul_pow, hrpowSq, hhalfSq, Real.sq_sqrt hnu]
  have hsq : osc ^ 2 ≤
      (C * r ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt nu) ^ 2 := by
    calc
      osc ^ 2 ≤ C ^ 2 * r ^ (2 - (d : ℝ)) * s⁻¹ * nu := hbound
      _ = (C * r ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt nu) ^ 2 :=
        hrightSq.symm
  have hsqAbs : |osc| ^ 2 ≤
      (C * r ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt nu) ^ 2 := by
    rw [sq_abs]
    exact hsq
  have habs : |osc| ≤ C * r ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt nu :=
    (sq_le_sq₀ (abs_nonneg osc) hright).mp hsqAbs
  exact le_trans (le_abs_self osc) habs

/-- Squaring the sourced Hölder bound yields the reference-ratio local-energy estimate. -/
theorem trace_energy_le_reference_ratio
    (d : ℕ) (trace C Ce r se sf nu f energy : ℝ)
    (htrace : 0 ≤ trace) (hC : 0 ≤ C) (hCe : 0 ≤ Ce)
    (hr : 0 < r) (hse : 0 < se) (hsf : 0 ≤ sf) (hnu : 0 ≤ nu) (hf : 0 ≤ f)
    (hTrace : trace ≤ C * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu +
      C * r ^ (2 : ℝ) * se⁻¹ * f)
    (hEnergy : energy ≤ Ce * sf * r ^ ((d : ℝ) - 2) * trace ^ 2) :
    energy ≤ (2 * Ce * C ^ 2) * (sf / se) *
      (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2) := by
  let A : ℝ := C * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu
  let B : ℝ := C * r ^ (2 : ℝ) * se⁻¹ * f
  let K : ℝ := Ce * sf * r ^ ((d : ℝ) - 2)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hr.le _))
      (Real.rpow_nonneg hse.le _)) (Real.sqrt_nonneg _)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hr.le _))
      (inv_nonneg.mpr hse.le)) hf
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hCe hsf) (Real.rpow_nonneg hr.le _)
  have hsum : trace ≤ A + B := hTrace
  have htraceSq : trace ^ 2 ≤ (A + B) ^ 2 :=
    (sq_le_sq₀ htrace (add_nonneg hA hB)).mpr hsum
  have htwo : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    nlinarith only [sq_nonneg (A - B)]
  have hRpowSq : (r ^ ((2 - (d : ℝ)) / 2)) ^ 2 = r ^ (2 - (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    ring
  have hRfourSq : (r ^ (2 : ℝ)) ^ 2 = r ^ (4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    ring
  have hhalfSq : (se ^ (-(1 : ℝ) / 2)) ^ 2 = se⁻¹ := by
    have hexp : (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) := by ring
    rw [hexp, rpow_neg_half_sq hse]
  have hAsq : A ^ 2 = C ^ 2 * r ^ (2 - (d : ℝ)) * se⁻¹ * nu := by
    dsimp [A]
    rw [mul_pow, mul_pow, mul_pow, hRpowSq, hhalfSq, Real.sq_sqrt hnu]
  have hBsq : B ^ 2 = C ^ 2 * r ^ (4 : ℝ) * (se⁻¹) ^ 2 * f ^ 2 := by
    dsimp [B]
    rw [mul_pow, mul_pow, mul_pow, hRfourSq]
  have hrCancel : r ^ ((d : ℝ) - 2) * r ^ (2 - (d : ℝ)) = 1 := by
    rw [← Real.rpow_add hr]
    have hexp : ((d : ℝ) - 2) + (2 - (d : ℝ)) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have hrCombine : r ^ ((d : ℝ) - 2) * r ^ (4 : ℝ) = r ^ ((d : ℝ) + 2) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hAterm : K * (2 * A ^ 2) = (2 * Ce * C ^ 2) * (sf / se) * nu := by
    rw [hAsq]
    calc
      Ce * sf * r ^ ((d : ℝ) - 2) *
          (2 * (C ^ 2 * r ^ (2 - (d : ℝ)) * se⁻¹ * nu)) =
          (2 * Ce * C ^ 2) *
            (sf * (r ^ ((d : ℝ) - 2) * r ^ (2 - (d : ℝ))) * se⁻¹ * nu) := by ring
      _ = (2 * Ce * C ^ 2) * (sf / se) * nu := by
        rw [hrCancel, div_eq_mul_inv]
        ring
  have hBterm : K * (2 * B ^ 2) =
      (2 * Ce * C ^ 2) * (sf / se) * (se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2) := by
    rw [hBsq]
    calc
      Ce * sf * r ^ ((d : ℝ) - 2) *
          (2 * (C ^ 2 * r ^ (4 : ℝ) * (se⁻¹) ^ 2 * f ^ 2)) =
          (2 * Ce * C ^ 2) *
            (sf * (r ^ ((d : ℝ) - 2) * r ^ (4 : ℝ)) * (se⁻¹) ^ 2 * f ^ 2) := by ring
      _ = (2 * Ce * C ^ 2) * (sf / se) * (se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2) := by
        rw [hrCombine, div_eq_mul_inv]
        ring
  have hsumTerms : K * (2 * A ^ 2 + 2 * B ^ 2) =
      (2 * Ce * C ^ 2) * (sf / se) *
        (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2) := by
    calc
      K * (2 * A ^ 2 + 2 * B ^ 2) = K * (2 * A ^ 2) + K * (2 * B ^ 2) := by rw [mul_add]
      _ = (2 * Ce * C ^ 2) * (sf / se) * nu +
          (2 * Ce * C ^ 2) * (sf / se) * (se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2) := by
        rw [hAterm, hBterm]
      _ = (2 * Ce * C ^ 2) * (sf / se) *
          (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2) := by ring
  calc
    energy ≤ Ce * sf * r ^ ((d : ℝ) - 2) * trace ^ 2 := hEnergy
    _ = K * trace ^ 2 := rfl
    _ ≤ K * (2 * A ^ 2 + 2 * B ^ 2) := by
      exact mul_le_mul_of_nonneg_left (le_trans htraceSq htwo) hK
    _ = (2 * Ce * C ^ 2) * (sf / se) *
        (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2) := hsumTerms

end SubdiffusiveProcess
