import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! An affine bound on finitely many allowances controls their discounted
exponential product when the spatial discount pays the linear depth loss.
No moment bound or almost-sure assertion is made.
-/
open scoped BigOperators
namespace SubdiffusiveProcess

/-- A spatial discount absorbs the linear part of a finite allowance sum. -/
theorem discounted_allowance_product_le {ι : Type*} [Fintype ι]
    (B : ι → ℝ) (n : ℕ) (xi b eta c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hB : ∀ i, B i ≤ xi * n + b)
    (hgap : c * Fintype.card ι * xi ≤ eta * Real.log 3) :
    (3 : ℝ) ^ (-eta * (n : ℝ)) * (C * Real.exp (c * ∑ i, B i)) ≤
      C * Real.exp (c * Fintype.card ι * b) := by
  have hsum : (∑ i, B i) ≤ (Fintype.card ι : ℝ) * (xi * n + b) := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hB i)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  have he : Real.log 3 * (-eta * (n : ℝ)) + c * ∑ i, B i ≤
      c * Fintype.card ι * b := by
    have hh := mul_le_mul_of_nonneg_left hsum hc
    have hn := mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [hh, hn]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  calc Real.exp (Real.log 3 * (-eta * (n : ℝ))) * (C * Real.exp (c * ∑ i, B i)) =
      C * Real.exp (Real.log 3 * (-eta * (n : ℝ)) + c * ∑ i, B i) := by
        rw [Real.exp_add]
        ring
    _ ≤ C * Real.exp (c * Fintype.card ι * b) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC

/-- Positive allowance and tail slopes can meet both the deterministic loss and spatial entropy budgets. -/
theorem exists_mesh_allowance_slopes (d : ℕ) (c eta : ℝ) (hc : 0 ≤ c) (heta : 0 < eta) :
    ∃ xi A : ℝ, 0 < xi ∧ 0 < A ∧
      c * (d + 1 : ℕ) * xi ≤ eta * Real.log 3 ∧ (d : ℝ) * Real.log 3 < A * xi := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < c * (d + 1 : ℕ) + 1 := by positivity
  let xi := eta * Real.log 3 / (c * (d + 1 : ℕ) + 1)
  have hxi : 0 < xi := div_pos (mul_pos heta hlog) hden
  let A := ((d : ℝ) * Real.log 3 + 1) / xi
  have hA : 0 < A := div_pos (by positivity) hxi
  refine ⟨xi, A, hxi, hA, ?_, ?_⟩
  · have heq : xi * (c * (d + 1 : ℕ) + 1) = eta * Real.log 3 := div_mul_cancel₀ _ hden.ne'
    nlinarith only [heq, hxi]
  · have heq : A * xi = (d : ℝ) * Real.log 3 + 1 := div_mul_cancel₀ _ hxi.ne'
    linarith only [heq]

end SubdiffusiveProcess
