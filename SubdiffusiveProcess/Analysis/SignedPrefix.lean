module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Signed finite prefixes on integer levels telescope across zero. This is
finite algebra; no convergence of the underlying two-sided sequence is asserted.
-/
open scoped BigOperators
namespace SubdiffusiveProcess

/-- The prefix from zero to an integer endpoint, with the usual signed orientation. -/
def signedPrefix (f : ℤ → ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k then ∑ i ∈ Finset.Ico 0 k, f i else -∑ i ∈ Finset.Ico k 0, f i

/-- Consecutive ordered integer interval sums concatenate. -/
theorem int_sum_Ico_add (f : ℤ → ℝ) (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ i ∈ Finset.Ico a b, f i) + (∑ i ∈ Finset.Ico b c, f i) =
      ∑ i ∈ Finset.Ico a c, f i := by
  rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c),
    Finset.Ico_union_Ico_eq_Ico hab hbc]

/-- Two ordered signed prefixes differ by their literal interval sum. -/
theorem signedPrefix_sub (f : ℤ → ℝ) (k l : ℤ) (hkl : k ≤ l) :
    signedPrefix f l - signedPrefix f k = ∑ i ∈ Finset.Ico k l, f i := by
  by_cases hk : 0 ≤ k
  · have hl := hk.trans hkl
    rw [signedPrefix, ite_eq_left hl, signedPrefix, ite_eq_left hk]
    have hh := int_sum_Ico_add f 0 k l hk hkl
    linarith only [hh]
  · by_cases hl : 0 ≤ l
    · rw [signedPrefix, ite_eq_left hl, signedPrefix, ite_eq_right hk]
      have hh := int_sum_Ico_add f k 0 l (le_of_not_ge hk) hl
      linarith only [hh]
    · rw [signedPrefix, ite_eq_right hl, signedPrefix, ite_eq_right hk]
      have hh := int_sum_Ico_add f k l 0 hkl (le_of_not_ge hl)
      linarith only [hh]

end SubdiffusiveProcess
