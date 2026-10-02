import SubdiffusiveProcess.Analysis.BufferedScoreWindow

/-! Exact reflection of a finite scale window about a cutoff, and the
nonnegative subwindow comparison. These are finite sums with no analytic or
probabilistic assertions.
-/
open scoped BigOperators
namespace SubdiffusiveProcess

/-- Reflection about a cutoff identifies an integer scale sum with its native window. -/
theorem sum_reflected_scale_window (N n m : ℕ) (hnm : n ≤ m) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc ((N : ℤ) - m) ((N : ℤ) - n), f ((N : ℤ) - i).toNat) =
      ∑ j ∈ Finset.Icc n m, f j := by
  apply Finset.sum_bij (fun i _ => ((N : ℤ) - i).toNat)
  · intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro i hi i' hi' heq
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
    obtain ⟨hlo', hhi'⟩ := Finset.mem_Icc.mp hi'
    omega
  · intro j hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
    refine ⟨(N : ℤ) - j, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩ <;> omega
  · intro i hi
    rfl

/-- A reflected subwindow has no more mass than the nonnegative native window. -/
theorem sum_reflected_subwindow_le (N n m : ℕ) (hnm : n ≤ m)
    (a b : ℤ) (ha : (N : ℤ) - m ≤ a) (hb : b ≤ (N : ℤ) - n)
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ i ∈ Finset.Ico a b, f ((N : ℤ) - i).toNat) ≤
      ∑ j ∈ Finset.Icc n m, f j := by
  rw [← sum_reflected_scale_window N n m hnm f]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
    exact Finset.mem_Icc.mpr ⟨ha.trans hlo, hhi.le.trans hb⟩
  · intro i hi hnot
    exact hf _

end SubdiffusiveProcess
