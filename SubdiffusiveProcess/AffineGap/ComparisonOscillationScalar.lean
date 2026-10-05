module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! # Scalar conversion of the comparison-cube Poincaré bound

With `m = 729 R`, a Poincaré bound `N² ≤ K m² m^{-d} σ⁻¹ Γ` for the centered oscillation on the
comparison cube, a ratio bound `σ⁻¹ ≤ 2 s⁻¹` and the parent condition `Γ ≤ L^{d+ζ} S` give
`729^{d/2} N ≤ C R^{(2-d)/2} L̃^{(d+ζ)/2} √(S/s)` once `729 √(2K) (L/L̃)^{(d+ζ)/2} ≤ C`.
Purely real arithmetic. -/

noncomputable section
namespace SubdiffusiveProcess

/-- The comparison-cube oscillation is bounded at the comparison scale by the parent budget. -/
theorem comparison_oscillation_scalar (d : ℕ) (N K m R L Lt zeta C S s sig Gam : ℝ)
    (hR : 0 < R) (hm : m = 729 * R) (hK : 0 ≤ K) (hs : 0 < s)
    (hratio : sig⁻¹ ≤ 2 * s⁻¹) (hS : 0 ≤ S) (hGam0 : 0 ≤ Gam)
    (hGam : Gam ≤ L ^ ((d : ℝ) + zeta) * S) (hLt : 0 < Lt) (hLLt : Lt ≤ L)
    (hN0 : 0 ≤ N)
    (hN : N ^ 2 ≤ (K * m ^ 2 / m ^ d) * sig⁻¹ * Gam)
    (hC : 729 * Real.sqrt (2 * K) * (L / Lt) ^ (((d : ℝ) + zeta) / 2) ≤ C) :
    (729 : ℝ) ^ ((d : ℝ) / 2) * N ≤
      C * R ^ ((2 - (d : ℝ)) / 2) * Lt ^ (((d : ℝ) + zeta) / 2) * Real.sqrt (S / s) := by
  have hL : 0 < L := hLt.trans_le hLLt
  have hm0 : 0 < m := by rw [hm]; positivity
  have hsq : ∀ x : ℝ, 0 ≤ x → ∀ a : ℝ, (x ^ (a / 2)) ^ 2 = x ^ a := by
    intro x hx a
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    push_cast
    ring
  -- the square of the left side
  have hlhs : ((729 : ℝ) ^ ((d : ℝ) / 2) * N) ^ 2 ≤
      729 ^ 2 * (2 * K) * R ^ (2 - (d : ℝ)) * (L ^ ((d : ℝ) + zeta) * (S / s)) := by
    have hpow : (729 : ℝ) ^ (d : ℝ) * (m ^ 2 / m ^ d) = 729 ^ 2 * R ^ (2 - (d : ℝ)) := by
      rw [hm, ← Real.rpow_natCast (729 * R) d, ← Real.rpow_natCast (729 * R) 2,
        ← Real.rpow_sub (by positivity), Real.mul_rpow (by norm_num) hR.le,
        ← mul_assoc, ← Real.rpow_add (by norm_num)]
      norm_num
    have h729 : (0 : ℝ) ≤ 729 ^ (d : ℝ) := by positivity
    have hstep1 : ((729 : ℝ) ^ ((d : ℝ) / 2) * N) ^ 2 = 729 ^ (d : ℝ) * N ^ 2 := by
      rw [mul_pow, hsq 729 (by norm_num)]
    rw [hstep1]
    have hmd : 0 ≤ m ^ 2 / m ^ d := by positivity
    have hsig' : sig⁻¹ * Gam ≤ 2 * s⁻¹ * (L ^ ((d : ℝ) + zeta) * S) :=
      mul_le_mul hratio hGam hGam0 (by positivity)
    calc 729 ^ (d : ℝ) * N ^ 2 ≤ 729 ^ (d : ℝ) * ((K * m ^ 2 / m ^ d) * sig⁻¹ * Gam) :=
          mul_le_mul_of_nonneg_left hN h729
      _ = K * (729 ^ (d : ℝ) * (m ^ 2 / m ^ d)) * (sig⁻¹ * Gam) := by ring
      _ ≤ K * (729 ^ (d : ℝ) * (m ^ 2 / m ^ d)) * (2 * s⁻¹ * (L ^ ((d : ℝ) + zeta) * S)) :=
          mul_le_mul_of_nonneg_left hsig' (by positivity)
      _ = 729 ^ 2 * (2 * K) * R ^ (2 - (d : ℝ)) * (L ^ ((d : ℝ) + zeta) * (S / s)) := by
          rw [hpow]; field_simp
  -- the square of the right side
  have hrhs : 729 ^ 2 * (2 * K) * R ^ (2 - (d : ℝ)) * (L ^ ((d : ℝ) + zeta) * (S / s)) ≤
      (C * R ^ ((2 - (d : ℝ)) / 2) * Lt ^ (((d : ℝ) + zeta) / 2) * Real.sqrt (S / s)) ^ 2 := by
    have hC0 : 0 ≤ 729 * Real.sqrt (2 * K) * (L / Lt) ^ (((d : ℝ) + zeta) / 2) := by positivity
    have hCsq : (729 * Real.sqrt (2 * K) * (L / Lt) ^ (((d : ℝ) + zeta) / 2)) ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ hC0 hC 2
    have hexp : (729 * Real.sqrt (2 * K) * (L / Lt) ^ (((d : ℝ) + zeta) / 2)) ^ 2 =
        729 ^ 2 * (2 * K) * (L / Lt) ^ ((d : ℝ) + zeta) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hsq _ (by positivity)]
    have hLratio : L ^ ((d : ℝ) + zeta) = (L / Lt) ^ ((d : ℝ) + zeta) * Lt ^ ((d : ℝ) + zeta) := by
      rw [← Real.mul_rpow (by positivity) hLt.le, div_mul_cancel₀ _ hLt.ne']
    have hright : (C * R ^ ((2 - (d : ℝ)) / 2) * Lt ^ (((d : ℝ) + zeta) / 2) *
        Real.sqrt (S / s)) ^ 2 =
        C ^ 2 * R ^ (2 - (d : ℝ)) * Lt ^ ((d : ℝ) + zeta) * (S / s) := by
      rw [mul_pow, mul_pow, mul_pow, hsq _ hR.le, hsq _ hLt.le,
        Real.sq_sqrt (div_nonneg hS hs.le)]
    rw [hright, hLratio]
    have hX : 0 ≤ R ^ (2 - (d : ℝ)) * Lt ^ ((d : ℝ) + zeta) * (S / s) := by positivity
    calc 729 ^ 2 * (2 * K) * R ^ (2 - (d : ℝ)) *
          ((L / Lt) ^ ((d : ℝ) + zeta) * Lt ^ ((d : ℝ) + zeta) * (S / s))
        = (729 ^ 2 * (2 * K) * (L / Lt) ^ ((d : ℝ) + zeta)) *
          (R ^ (2 - (d : ℝ)) * Lt ^ ((d : ℝ) + zeta) * (S / s)) := by ring
      _ ≤ C ^ 2 * (R ^ (2 - (d : ℝ)) * Lt ^ ((d : ℝ) + zeta) * (S / s)) := by
          rw [← hexp]; exact mul_le_mul_of_nonneg_right hCsq hX
      _ = _ := by ring
  have hT0 : 0 ≤ C * R ^ ((2 - (d : ℝ)) / 2) * Lt ^ (((d : ℝ) + zeta) / 2) *
      Real.sqrt (S / s) := by
    have hC0 : 0 ≤ C := le_trans (by positivity) hC
    positivity
  have hA0 : 0 ≤ (729 : ℝ) ^ ((d : ℝ) / 2) * N := by positivity
  exact (pow_le_pow_iff_left₀ hA0 hT0 two_ne_zero).1 (hlhs.trans hrhs)

end SubdiffusiveProcess
