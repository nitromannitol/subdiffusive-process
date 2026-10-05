module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset




@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

open Finset

/-- The telescoping core of discrete Grönwall: the running partial sum plus `H` is
dominated by `H ∏ (1 + ε_k)`. -/
theorem gronwallProdBound {N : ℕ} {H : ℝ} {a ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k)
    (hrec : ∀ l ≤ N, a l ≤ H + ∑ k ∈ range l, ε k * a k) :
    ∀ l ≤ N, (∑ k ∈ range l, ε k * a k) + H ≤ H * ∏ k ∈ range l, (1 + ε k) := by
  intro l
  induction l with
  | zero => intro _; simp
  | succ l ih =>
      intro hlN
      have hlN' : l ≤ N := Nat.le_of_succ_le hlN
      have ihl := ih hlN'
      set S : ℝ := ∑ k ∈ range l, ε k * a k with hS
      set P : ℝ := ∏ k ∈ range l, (1 + ε k) with hP
      have hstep : a l ≤ H + S := by
        have h := hrec l hlN'
        rwa [← hS] at h
      have hmul : ε l * a l ≤ ε l * (H + S) :=
        mul_le_mul_of_nonneg_left hstep (hε l)
      have hfac : (0 : ℝ) ≤ 1 + ε l := by linarith only [hε l]
      have hstepprod : (S + H) * (1 + ε l) ≤ (H * P) * (1 + ε l) :=
        mul_le_mul_of_nonneg_right ihl hfac
      rw [Finset.sum_range_succ, Finset.prod_range_succ, ← hS, ← hP]
      calc (S + ε l * a l) + H
          ≤ (S + ε l * (H + S)) + H := by linarith only [hmul]
        _ = (S + H) * (1 + ε l) := by ring
        _ ≤ (H * P) * (1 + ε l) := hstepprod
        _ = H * (P * (1 + ε l)) := by ring

/-- **Discrete Grönwall**, all-indices form.

If `H ≥ 0`, the `ε_k` are nonnegative and `a_l ≤ H + ∑_{k<l} ε_k a_k` for every
`l ≤ N`, then `a_l ≤ H exp(∑_{k<l} ε_k)` for every `l ≤ N`. -/
theorem discrete_gronwall {N : ℕ} {H : ℝ} {a ε : ℕ → ℝ} (hH : 0 ≤ H)
    (hε : ∀ k, 0 ≤ ε k)
    (hrec : ∀ l ≤ N, a l ≤ H + ∑ k ∈ range l, ε k * a k) :
    ∀ l ≤ N, a l ≤ H * Real.exp (∑ k ∈ range l, ε k) := by
  intro l hlN
  have hprod := gronwallProdBound hε hrec l hlN
  have hstep : a l ≤ H + ∑ k ∈ range l, ε k * a k := hrec l hlN
  have hpe : ∏ k ∈ range l, (1 + ε k) ≤ Real.exp (∑ k ∈ range l, ε k) := by
    calc ∏ k ∈ range l, (1 + ε k)
        ≤ ∏ k ∈ range l, Real.exp (ε k) := by
          refine Finset.prod_le_prod₀ (fun k _ => ?_) fun k _ => ?_
          · linarith only [hε k]
          · linarith only [Real.add_one_le_exp (ε k)]
      _ = Real.exp (∑ k ∈ range l, ε k) := (Real.exp_sum _ _).symm
  have hHprod : H * ∏ k ∈ range l, (1 + ε k) ≤ H * Real.exp (∑ k ∈ range l, ε k) :=
    mul_le_mul_of_nonneg_left hpe hH
  linarith only [hprod, hstep, hHprod]

/-- **Discrete Grönwall**, the source's literal single-index conclusion. -/
theorem discrete_gronwall_top {N : ℕ} {H : ℝ} {a ε : ℕ → ℝ} (hH : 0 ≤ H)
    (hε : ∀ k, 0 ≤ ε k)
    (hrec : ∀ l ≤ N, a l ≤ H + ∑ k ∈ range l, ε k * a k) :
    a N ≤ H * Real.exp (∑ k ∈ range N, ε k) :=
  discrete_gronwall hH hε hrec N le_rfl

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
