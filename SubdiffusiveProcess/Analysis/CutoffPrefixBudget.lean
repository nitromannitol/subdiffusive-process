module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

@[expose] public section

/-! Arithmetic for prefix events not covered by a shallow cutoff catalogue.
A linear cutoff budget has only a linear cost in prefix length, which is
absorbed by half of an exponential tail rate. No probabilistic claim is made.
-/
namespace SubdiffusiveProcess

/-- A linear factor costs a fixed constant when one exponential rate is reserved. -/
theorem linear_mul_exp_double_le (A x : ℝ) (hA : 0 < A) (hx : 0 ≤ x) :
    (x + 1) * Real.exp (-(2 * A * x)) ≤
      (1 + A⁻¹) * Real.exp (-(A * x)) := by
  have hexp : 1 ≤ Real.exp (A * x) := Real.one_le_exp (mul_nonneg hA.le hx)
  have hAx : A * x ≤ Real.exp (A * x) := by
    linarith only [Real.add_one_le_exp (A * x)]
  have hxexp : x ≤ A⁻¹ * Real.exp (A * x) := by
    apply le_of_mul_le_mul_left (a := A) (b := x) (c := A⁻¹ * Real.exp (A * x)) ?_ hA
    calc A * x ≤ Real.exp (A * x) := hAx
      _ = A * (A⁻¹ * Real.exp (A * x)) := by rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]
  have hsum : x + 1 ≤ (1 + A⁻¹) * Real.exp (A * x) := by
    nlinarith only [hxexp, hexp]
  calc (x + 1) * Real.exp (-(2 * A * x)) ≤
      ((1 + A⁻¹) * Real.exp (A * x)) * Real.exp (-(2 * A * x)) :=
        mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
    _ = (1 + A⁻¹) * Real.exp (-(A * x)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The integer cutoff budget covers every linear bound once length dominates root depth. -/
theorem cutoff_prefix_budget_covers (c xi : ℝ) (buffer n m N : ℕ)
    (hc : 0 ≤ c) (hxi : 0 < xi) (hdepth : xi * n ≤ (m : ℝ))
    (hN : (N : ℝ) ≤ c * ((n : ℝ) + m + buffer)) :
    N ≤ ⌈(c * (xi⁻¹ + 1 + buffer) + 1) * ((m : ℝ) + 1)⌉₊ := by
  have hn : (n : ℝ) ≤ xi⁻¹ * m := by
    apply le_of_mul_le_mul_left (a := xi) (b := (n : ℝ)) (c := xi⁻¹ * m) ?_ hxi
    simpa only [← mul_assoc, mul_inv_cancel₀ hxi.ne', one_mul] using hdepth
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ buffer := Nat.cast_nonneg _
  have hi : 0 ≤ xi⁻¹ := inv_nonneg.mpr hxi.le
  have hbudget : c * ((n : ℝ) + m + buffer) ≤
      (c * (xi⁻¹ + 1 + buffer) + 1) * ((m : ℝ) + 1) := by
    nlinarith only [hn, hm, hb, hi, hc, mul_nonneg hc hi,
      mul_nonneg hc hb, mul_nonneg (mul_nonneg hc hb) hm]
  exact_mod_cast (hN.trans hbudget).trans (Nat.le_ceil _)

/-- The integer cutoff budget always includes the prefix length itself. -/
theorem cutoff_prefix_budget_ge_length (c xi : ℝ) (buffer m : ℕ)
    (hc : 0 ≤ c) (hxi : 0 < xi) :
    m ≤ ⌈(c * (xi⁻¹ + 1 + buffer) + 1) * ((m : ℝ) + 1)⌉₊ := by
  have hcoef : 0 ≤ c * (xi⁻¹ + 1 + buffer) := by positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hle : (m : ℝ) ≤ (c * (xi⁻¹ + 1 + buffer) + 1) * ((m : ℝ) + 1) := by
    nlinarith only [hcoef, hm, mul_nonneg hcoef hm]
  exact_mod_cast hle.trans (Nat.le_ceil _)

/-- Counting all cutoffs through the integer budget costs at most a linear factor. -/
theorem cutoff_prefix_budget_card_le (c xi : ℝ) (buffer m : ℕ)
    (hc : 0 ≤ c) (hxi : 0 < xi) :
    (⌈(c * (xi⁻¹ + 1 + buffer) + 1) * ((m : ℝ) + 1)⌉₊ : ℝ) + 1 ≤
      (c * (xi⁻¹ + 1 + buffer) + 3) * ((m : ℝ) + 1) := by
  have harg : 0 ≤ (c * (xi⁻¹ + 1 + buffer) + 1) * ((m : ℝ) + 1) := by positivity
  have hceil := Nat.ceil_lt_add_one harg
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith only [hceil, hm]

end SubdiffusiveProcess
