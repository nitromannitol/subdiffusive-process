module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveTest

@[expose] public section

/-!
# Pointwise algebra for the direct boundary coercive test

This file isolates the Young-inequality calculation after testing the scalar
divergence-form equation with `eta^2 (u-h)`.  The constants are deliberately
non-sharp; the harmonic-approximation anchor only requires a dimension-only
constant.

PROVENANCE: this is the scalar-coefficient specialization of the energy
absorption in CoarseGraining's `WeakInteriorDQ/EnergyIntegrand.lean`, with the
two datum terms retained instead of setting the boundary datum to zero.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization

noncomputable section

variable {d : ℕ}

/-- The expanded right-hand side of the direct squared-cutoff identity is
bounded pointwise by three eighths of the main energy plus datum, cutoff, and
forcing prices. -/
theorem scalar_boundary_coercive_rhs_le
    {a eta w : ℝ} {U H G E : Vec d} (ha : 0 < a) :
    a * eta ^ 2 * vecDot U H -
        2 * a * eta * w * vecDot U E -
        eta ^ 2 * vecDot G U + eta ^ 2 * vecDot G H -
        2 * eta * w * vecDot G E ≤
      (3 / 8 : ℝ) * (a * eta ^ 2 * vecNormSq U) +
        (5 / 2 : ℝ) * (a * eta ^ 2 * vecNormSq H) +
        (17 / 2 : ℝ) * (a * w ^ 2 * vecNormSq E) +
        (9 / 2 : ℝ) * (a⁻¹ * eta ^ 2 * vecNormSq G) := by
  let r : ℝ := Real.sqrt a
  have hr : 0 < r := Real.sqrt_pos.2 ha
  have hr0 : r ≠ 0 := hr.ne'
  have hrsq : r ^ 2 = a := by
    dsimp [r]
    exact Real.sq_sqrt ha.le
  have hrmul : r * r = a := by simpa [pow_two] using hrsq
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
  have hinvsq : (r⁻¹) ^ 2 = a⁻¹ := by
    rw [inv_pow, hrsq]
  have hUHraw :=
    abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (r * eta / 2) (2 * r * eta) U H
  have hUH :
      |a * eta ^ 2 * vecDot U H| ≤
        (a * eta ^ 2 * vecNormSq U) / 8 +
          2 * a * eta ^ 2 * vecNormSq H := by
    calc
      |a * eta ^ 2 * vecDot U H| =
          |(r * eta / 2) * (2 * r * eta) * vecDot U H| := by
        congr 1
        rw [← hrmul]
        ring
      _ ≤ _ := hUHraw
      _ = _ := by rw [← hrsq]; ring
  have hUEraw :=
    abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (r * eta / 2) (4 * r * w) U E
  have hUE :
      |2 * a * eta * w * vecDot U E| ≤
        (a * eta ^ 2 * vecNormSq U) / 8 +
          8 * a * w ^ 2 * vecNormSq E := by
    calc
      |2 * a * eta * w * vecDot U E| =
          |(r * eta / 2) * (4 * r * w) * vecDot U E| := by
        congr 1
        rw [← hrmul]
        ring
      _ ≤ _ := hUEraw
      _ = _ := by rw [← hrsq]; ring
  have hGUraw :=
    abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (r * eta / 2) (2 * eta * r⁻¹) U G
  have hGU :
      |eta ^ 2 * vecDot G U| ≤
        (a * eta ^ 2 * vecNormSq U) / 8 +
          2 * a⁻¹ * eta ^ 2 * vecNormSq G := by
    rw [vecDot_comm]
    calc
      |eta ^ 2 * vecDot U G| =
          |(r * eta / 2) * (2 * eta * r⁻¹) * vecDot U G| := by
        congr 1
        rw [show r * eta / 2 * (2 * eta * r⁻¹) = eta ^ 2 by
          calc
            r * eta / 2 * (2 * eta * r⁻¹) = (r * r⁻¹) * eta ^ 2 := by ring
            _ = eta ^ 2 := by rw [hinv, one_mul]]
      _ ≤ _ := hGUraw
      _ = _ := by rw [← hrsq]; field_simp [hr0]; ring
  have hGHraw :=
    abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (r * eta) (eta * r⁻¹) H G
  have hGH :
      |eta ^ 2 * vecDot G H| ≤
        (a * eta ^ 2 * vecNormSq H) / 2 +
          (a⁻¹ * eta ^ 2 * vecNormSq G) / 2 := by
    rw [vecDot_comm]
    calc
      |eta ^ 2 * vecDot H G| =
          |(r * eta) * (eta * r⁻¹) * vecDot H G| := by
        congr 1
        rw [show (r * eta) * (eta * r⁻¹) = eta ^ 2 by
          calc
            (r * eta) * (eta * r⁻¹) = (r * r⁻¹) * eta ^ 2 := by ring
            _ = eta ^ 2 := by rw [hinv, one_mul]]
      _ ≤ _ := hGHraw
      _ = _ := by rw [← hrsq]; field_simp [hr0]
  have hGEraw :=
    abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (r * w) (2 * eta * r⁻¹) E G
  have hGE :
      |2 * eta * w * vecDot G E| ≤
        (a * w ^ 2 * vecNormSq E) / 2 +
          2 * a⁻¹ * eta ^ 2 * vecNormSq G := by
    rw [vecDot_comm]
    calc
      |2 * eta * w * vecDot E G| =
          |(r * w) * (2 * eta * r⁻¹) * vecDot E G| := by
        congr 1
        rw [show (r * w) * (2 * eta * r⁻¹) = 2 * eta * w by
          calc
            (r * w) * (2 * eta * r⁻¹) = (r * r⁻¹) * (2 * eta * w) := by ring
            _ = 2 * eta * w := by rw [hinv, one_mul]]
      _ ≤ _ := hGEraw
      _ = _ := by rw [← hrsq]; field_simp [hr0]
  have hUH' := (le_abs_self (a * eta ^ 2 * vecDot U H)).trans hUH
  have hUE' := (neg_le_abs (2 * a * eta * w * vecDot U E)).trans hUE
  have hGU' := (neg_le_abs (eta ^ 2 * vecDot G U)).trans hGU
  have hGH' := (le_abs_self (eta ^ 2 * vecDot G H)).trans hGH
  have hGE' := (neg_le_abs (2 * eta * w * vecDot G E)).trans hGE
  linarith only [hUH', hUE', hGU', hGH', hGE']

/-- Pointwise coercivity when the main energy equals the expanded direct-test
right-hand side. -/
theorem scalar_boundary_coercive_of_identity
    {a eta w : ℝ} {U H G E : Vec d} (ha : 0 < a)
    (hid :
      a * eta ^ 2 * vecNormSq U =
        a * eta ^ 2 * vecDot U H -
          2 * a * eta * w * vecDot U E -
          eta ^ 2 * vecDot G U + eta ^ 2 * vecDot G H -
          2 * eta * w * vecDot G E) :
    a * eta ^ 2 * vecNormSq U ≤
      4 * a * eta ^ 2 * vecNormSq H +
        14 * a * w ^ 2 * vecNormSq E +
        8 * a⁻¹ * eta ^ 2 * vecNormSq G := by
  have hbound := scalar_boundary_coercive_rhs_le (d := d)
    (a := a) (eta := eta) (w := w) (U := U) (H := H) (G := G) (E := E) ha
  have hX0 : 0 ≤ a * eta ^ 2 * vecNormSq U :=
    mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) (vecNormSq_nonneg _)
  have hH0 : 0 ≤ a * eta ^ 2 * vecNormSq H :=
    mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) (vecNormSq_nonneg _)
  have hE0 : 0 ≤ a * w ^ 2 * vecNormSq E :=
    mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) (vecNormSq_nonneg _)
  have hG0 : 0 ≤ a⁻¹ * eta ^ 2 * vecNormSq G :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr ha.le) (sq_nonneg _))
      (vecNormSq_nonneg _)
  nlinarith only [hid, hbound, hX0, hH0, hE0, hG0]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
