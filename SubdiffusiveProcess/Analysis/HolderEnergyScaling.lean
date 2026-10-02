import SubdiffusiveProcess.Sobolev.CoarseEnergyArithmetic
import Mathlib.Tactic

/-! Scalar scaling identities for an interior Holder energy estimate.
This module does not assert any analytic regularity or coefficient bound. -/

noncomputable section
namespace SubdiffusiveProcess

/-- The radius divided by square-root volume has the energy scaling exponent. -/
theorem radius_div_sqrt_volume (d : ℕ) (r : ℝ) (hr : 0 < r) :
    r / Real.sqrt (r ^ d) = r ^ ((2 - (d : ℝ)) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  calc r / r ^ ((d : ℝ) * (1 / 2)) = r ^ (1 : ℝ) / r ^ ((d : ℝ) * (1 / 2)) := by
        rw [Real.rpow_one]
    _ = r ^ ((2 - (d : ℝ)) / 2) := by
      rw [← Real.rpow_sub hr]
      congr 1
      ring

/-- An inner radius can be enlarged after multiplication by the Holder dilation weight. -/
theorem holder_radius_weight_le {r l alpha : ℝ} (hr : 0 < r) (hl : 0 ≤ l)
    (hlr : l ≤ r) (halpha : alpha ≤ 1) :
    r ^ alpha * l ^ (1 - alpha) ≤ r := by
  calc r ^ alpha * l ^ (1 - alpha) ≤ r ^ alpha * r ^ (1 - alpha) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hl hlr (sub_nonneg.mpr halpha)) (Real.rpow_nonneg hr.le _)
    _ = r := by rw [← Real.rpow_add hr, add_sub_cancel, Real.rpow_one]

/-- A reference comparison controls the inverse square root with one uniform factor. -/
theorem inv_sqrt_le_reference_factor {s b B : ℝ} (hs : 0 < s) (hb : 0 < b)
    (hB : 1 ≤ B) (hcomp : s ≤ B * b) :
    (Real.sqrt b)⁻¹ ≤ B * s ^ (-(1 : ℝ) / 2) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hBsq : Real.sqrt B ≤ B := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hB0.le, by nlinarith only [hB]⟩
  have hcmp : Real.sqrt s ≤ B * Real.sqrt b := by
    calc Real.sqrt s ≤ Real.sqrt (B * b) := Real.sqrt_le_sqrt hcomp
      _ = Real.sqrt B * Real.sqrt b := Real.sqrt_mul hB0.le b
      _ ≤ B * Real.sqrt b := mul_le_mul_of_nonneg_right hBsq (Real.sqrt_nonneg b)
  rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hs.le,
    ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hs)).mpr
  apply (inv_mul_le_iff₀ (Real.sqrt_pos.mpr hb)).mpr
  simpa only [mul_comm] using hcmp

/-- A positive reference comparison controls the reciprocal coefficient. -/
theorem inv_le_reference_factor {s a B : ℝ} (hs : 0 < s) (ha : 0 < a)
    (hcomp : s ≤ B * a) : a⁻¹ ≤ B * s⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hs).mpr
  apply (inv_mul_le_iff₀ ha).mpr
  simpa only [mul_comm] using hcomp

/-- The rescaled Morrey estimate has the native energy and bounded-source powers of the radius. -/
theorem holder_energy_scaling_le (d : ℕ) (r alpha A CM C B s a b E Kf : ℝ)
    (hr : 0 < r) (halpha : alpha ≤ 1) (hA : 0 ≤ A) (hCM : 0 ≤ CM) (hC : 0 ≤ C)
    (hB : 1 ≤ B) (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) (hKf : 0 ≤ Kf)
    (hcompA : s ≤ B * a) (hcompB : s ≤ B * b) :
    A * (r ^ alpha * (CM * (r / 2) ^ (1 - alpha) *
      (C * (Real.sqrt E / Real.sqrt b / Real.sqrt ((2 * r) ^ d)) +
        C * (r / 2) * a⁻¹ * Kf))) ≤
      (A * CM * C * B) * r ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt E +
        (A * CM * C * B) * r ^ (2 : ℝ) * s⁻¹ * Kf := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hsroot := inv_sqrt_le_reference_factor hs hb hB hcompB
  have hsrec := inv_le_reference_factor hs ha hcompA
  have hden : Real.sqrt (r ^ d) ≤ Real.sqrt ((2 * r) ^ d) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ hr.le (by linarith only [hr]) d)
  have hgrad : Real.sqrt E / Real.sqrt b / Real.sqrt ((2 * r) ^ d) ≤
      B * s ^ (-(1 : ℝ) / 2) * Real.sqrt E / Real.sqrt (r ^ d) := by
    calc _ ≤ (Real.sqrt E / Real.sqrt b) / Real.sqrt (r ^ d) :=
          div_le_div_of_nonneg_left (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (Real.sqrt_pos.mpr (pow_pos hr d)) hden
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        simpa only [div_eq_mul_inv, mul_comm] using
          mul_le_mul_of_nonneg_right hsroot (Real.sqrt_nonneg E)
  have hsource : (r / 2) * a⁻¹ * Kf ≤ r * (B * s⁻¹) * Kf := by
    apply mul_le_mul_of_nonneg_right _ hKf
    exact mul_le_mul (by linarith only [hr] : r / 2 ≤ r) hsrec
      (inv_nonneg.mpr ha.le) hr.le
  have hweight := holder_radius_weight_le hr (by positivity : 0 ≤ r / 2)
    (by linarith only [hr] : r / 2 ≤ r) halpha
  have hinter := add_le_add hgrad hsource
  have hinner0 : 0 ≤ Real.sqrt E / Real.sqrt b / Real.sqrt ((2 * r) ^ d) +
      (r / 2) * a⁻¹ * Kf := by positivity
  calc _ = (A * CM * C) * (r ^ alpha * (r / 2) ^ (1 - alpha)) *
        (Real.sqrt E / Real.sqrt b / Real.sqrt ((2 * r) ^ d) + (r / 2) * a⁻¹ * Kf) := by ring
    _ ≤ (A * CM * C) * r *
        (B * s ^ (-(1 : ℝ) / 2) * Real.sqrt E / Real.sqrt (r ^ d) + r * (B * s⁻¹) * Kf) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hweight (mul_nonneg (mul_nonneg hA hCM) hC))
        hinter hinner0 (mul_nonneg (mul_nonneg (mul_nonneg hA hCM) hC) hr.le)
    _ = (A * CM * C * B) * (r / Real.sqrt (r ^ d)) * s ^ (-(1 : ℝ) / 2) * Real.sqrt E +
        (A * CM * C * B) * r ^ (2 : ℝ) * s⁻¹ * Kf := by rw [Real.rpow_two]; ring
    _ = _ := by rw [radius_div_sqrt_volume d r hr]

end SubdiffusiveProcess
