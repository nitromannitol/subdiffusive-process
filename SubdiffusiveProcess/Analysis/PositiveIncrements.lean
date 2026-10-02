import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

open Filter Set
open scoped NNReal Topology BigOperators

namespace SubdiffusiveProcess

/-- Every nondecreasing nonnegative time vector is a limit of cumulative strictly positive increments. -/
theorem exists_positive_increments_tendsto
    {k : ℕ} (t : Fin k → ℝ≥0) (ht : Monotone t) :
    ∃ s : ℕ → Fin k → ℝ,
      (∀ n : ℕ, ∀ i : Fin k, 0 < s n i) ∧
      Tendsto (fun n : ℕ => fun i : Fin k =>
        Real.toNNReal (∑ j ∈ Finset.Iic i, s n j)) atTop (𝓝 t) := by
  let u : ℕ → Fin (k + 1) → ℝ := fun n i =>
    Fin.cases 0 (fun j => (t j : ℝ) + (j.val + 1 : ℝ) / (n + 1 : ℝ)) i
  let s : ℕ → Fin k → ℝ := fun n i => u n i.succ - u n i.castSucc
  refine ⟨s, ?_, ?_⟩
  · intro n i
    change 0 < u n i.succ - u n i.castSucc
    rw [sub_pos]
    cases k with
    | zero => exact Fin.elim0 i
    | succ k =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [u, Fin.cases_succ, Fin.castSucc_zero, Fin.cases_zero, Fin.val_zero,
          Nat.cast_zero, zero_add]
        positivity
      · simp only [u, Fin.cases_succ, Fin.castSucc_succ, Fin.val_succ]
        have hmono : (t j.castSucc : ℝ) ≤ (t j.succ : ℝ) := by
          exact_mod_cast ht (Fin.castSucc_le_succ j)
        have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
        have hfrac : (j.val + 1 : ℝ) / (n + 1 : ℝ) <
            (j.val + 1 + 1 : ℝ) / (n + 1 : ℝ) := by
          norm_num [Nat.cast_add, Nat.cast_one] at hn ⊢
          rw [div_lt_div_iff_of_pos_right hn]
          norm_num
        norm_num [Nat.cast_add, Nat.cast_one] at ⊢
        exact add_lt_add_of_le_of_lt hmono hfrac
  · apply tendsto_pi_nhds.2
    intro i
    have hsum : ∀ n : ℕ, (∑ j ∈ Finset.Iic i, s n j) = u n i.succ := by
      intro n
      have hinv : ∀ x : Fin (k + 1), u n 0 + Fin.partialSum (s n) x = u n x := by
        intro x
        induction x using Fin.inductionOn with
        | zero => simp [u]
        | succ x hx =>
          rw [Fin.partialSum_succ, ← add_assoc, hx]
          simp only [s]
          ring
      have hbridge : Fin.partialSum (s n) i.succ = ∑ j ∈ Finset.Iic i, s n j := by
        rw [Fin.partialSum_succ, ← Finset.sum_Iio_add_eq_sum_Iic]
        congr 1
        cases k with
        | zero => exact Fin.elim0 i
        | succ k =>
          induction i using Fin.inductionOn with
          | zero =>
            change Fin.partialSum (s n) 0 = _
            rw [Fin.partialSum_zero]
            symm
            apply Finset.sum_eq_zero
            intro j hj
            simp at hj
          | succ i ih =>
            rw [Fin.castSucc_succ, Fin.partialSum_succ, ih,
              Finset.sum_Iio_add_eq_sum_Iic]
            congr 1
      rw [← hbridge]
      simpa [u] using hinv i.succ
    simp_rw [hsum]
    simp only [u, Fin.cases_succ]
    have hreal : Tendsto (fun n : ℕ =>
        (t i : ℝ) + (i.val + 1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 (t i : ℝ)) := by
      have hfrac : Tendsto (fun n : ℕ =>
          (i.val + 1 : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      simpa only [add_zero, one_mul, div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (t i : ℝ)) atTop (𝓝 (t i : ℝ))).add hfrac
    simpa only [Real.toNNReal_coe] using tendsto_real_toNNReal hreal


end SubdiffusiveProcess
