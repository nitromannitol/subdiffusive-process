module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

/-! Finite moment banks can be dominated by a nonnegative bank at the same order.
Only integrability and finite summation are used; no independence is required. -/
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess.Probability

/-- A finite family of uniformly L1-bounded sequences has one nonnegative uniformly L1-bounded majorant. -/
theorem exists_finite_L1_majorant
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    (F : ι → ℕ → Ω → ℝ) (C : ι → ℝ≥0)
    (hmem : ∀ i n, MemLp (F i n) 1 P)
    (hnorm : ∀ i n, eLpNorm (F i n) 1 P ≤ C i) :
    ∃ (B : ℕ → Ω → ℝ) (CB : ℝ≥0),
      (∀ n om, 0 ≤ B n om) ∧ (∀ n, MemLp (B n) 1 P) ∧
      (∀ n, eLpNorm (B n) 1 P ≤ CB) ∧
      ∀ i n om, F i n om ≤ B n om := by
  classical
  let B : ℕ → Ω → ℝ := fun n om => ∑ i, ‖F i n om‖
  have hBm (n : ℕ) : MemLp (B n) 1 P := by
    exact memLp_finset_sum Finset.univ (fun i _ => (hmem i n).norm)
  have hBn (n : ℕ) : eLpNorm (B n) 1 P ≤ (∑ i, C i : ℝ≥0) := by
    calc
      _ ≤ ∑ i, eLpNorm (fun om => ‖F i n om‖) 1 P := by
        simpa only [B, Finset.sum_fn] using
          (eLpNorm_sum_le (f := fun i om => ‖F i n om‖) (s := Finset.univ)
            (le_rfl : (1 : ℝ≥0∞) ≤ 1))
      _ = ∑ i, eLpNorm (F i n) 1 P := by
        exact Finset.sum_congr rfl (fun i _ => eLpNorm_norm _ (hmem i n).aestronglyMeasurable)
      _ ≤ ∑ i, (C i : ℝ≥0∞) := Finset.sum_le_sum (fun i _ => hnorm i n)
      _ = _ := (ENNReal.ofNNReal_finsetSum _ _).symm
  refine ⟨B, ∑ i, C i, (fun n om => Finset.sum_nonneg fun i _ => norm_nonneg _),
    hBm, hBn, ?_⟩
  intro i n om
  exact (le_abs_self _).trans (Finset.single_le_sum
    (fun j _ => norm_nonneg (F j n om)) (Finset.mem_univ i))

end SubdiffusiveProcess.Probability
