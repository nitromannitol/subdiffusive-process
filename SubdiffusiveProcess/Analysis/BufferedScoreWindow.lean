import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! A reversed native scale window is contained in a buffered physical prefix.
This finite-sum comparison does not assume a stochastic score bound.
-/
open scoped BigOperators
namespace SubdiffusiveProcess

/-- Reversing native levels embeds their nonnegative sum into the physical buffered prefix. -/
theorem reflected_window_le_buffered (n m buffer : ℕ) (hnm : n ≤ m)
    (f : ℕ → ℝ) (g : ℤ → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hfg : ∀ j ∈ Finset.Icc n m, f j = g ((m : ℤ) - j)) :
    (∑ j ∈ Finset.Icc n m, f j) ≤
      ∑ i ∈ Finset.Icc (-(buffer : ℤ)) (((m - n : ℕ) : ℤ) + buffer), g i := by
  have hinj : Set.InjOn (fun j : ℕ => (m : ℤ) - j) (Finset.Icc n m : Set ℕ) := by
    intro a ha b hb hab
    dsimp only at hab
    omega
  calc (∑ j ∈ Finset.Icc n m, f j) =
      ∑ j ∈ Finset.Icc n m, g ((m : ℤ) - j) := Finset.sum_congr rfl hfg
    _ = ∑ i ∈ (Finset.Icc n m).image (fun j : ℕ => (m : ℤ) - j), g i :=
      (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hh := Finset.mem_Icc.mp hj
      apply Finset.mem_Icc.mpr
      constructor <;> omega) (fun i _ _ => hg i)

end SubdiffusiveProcess
