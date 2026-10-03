module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Integer prefix sums with a cutoff guard can be clipped at the cutoff.
These are finite-sum identities and impose no probabilistic assumptions.
-/

open scoped BigOperators

namespace SubdiffusiveProcess

/-- Terms above a cutoff contribute zero, so the upper endpoint may be clipped. -/
theorem sum_Icc_min_of_eq_zero_above (a b N : ℤ) (f : ℤ → ℝ)
    (hf : ∀ j, N < j → f j = 0) :
    ∑ j ∈ Finset.Icc a (min N b), f j = ∑ j ∈ Finset.Icc a b, f j := by
  apply Finset.sum_subset
  · intro j hj
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨ha, hb.trans (min_le_right N b)⟩
  · intro j hj hnot
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hj
    apply hf
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨ha, le_min (le_of_not_gt h) hb⟩)

/-- Translating the index of a finite integer prefix translates both endpoints. -/
theorem sum_Icc_translate (a b k : ℤ) (f : ℤ → ℝ) :
    ∑ j ∈ Finset.Icc a b, f (k + j) =
      ∑ j ∈ Finset.Icc (k + a) (k + b), f j := by
  apply Finset.sum_bij (fun j _ => k + j)
  · intro j hj
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j _ j' _ heq
    exact add_left_cancel heq
  · intro j hj
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hj
    refine ⟨j - k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩ <;> omega
  · intro j _
    rfl

end SubdiffusiveProcess
