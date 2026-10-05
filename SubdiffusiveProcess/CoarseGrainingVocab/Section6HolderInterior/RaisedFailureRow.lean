module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GateParameters

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Every summand of the failure row is nonnegative. -/
theorem failure_summand_nonneg (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (epsilon s : ℝ) (i : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ 1 - if omega ∈ goodEvent M none i z epsilon s then (1 : ℝ) else 0 := by
  by_cases h : omega ∈ goodEvent M none i z epsilon s <;> simp [h]

/-- **Restricting the failure row to a raised base.**  The control at base `b`
bounds the row at every base `b + c`. -/
theorem failure_row_restrict (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (epsilon s : ℝ) (b c m : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (∑ i ∈ Finset.Icc (b + c) m,
        (1 - if omega ∈ goodEvent M none i z epsilon s then (1 : ℝ) else 0)) ≤
      ∑ i ∈ Finset.Icc b m,
        (1 - if omega ∈ goodEvent M none i z epsilon s then (1 : ℝ) else 0) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro i _ _
    exact failure_summand_nonneg M epsilon s i z omega

/-- **The failure row at a raised base, in the shape the selection consumes.**

The base is raised from `b` to `b + c`, so the selected scale clears `b + c - 2`
rather than `b - 2`; with `c ≥ 5` this is the `j ≥ b + 3` the energy gate's
centre-proximity condition demands.  The price is the rate inflation `hinfl`,
which the ladder constant absorbs. -/
theorem raised_failure_row (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (epsilon s lambda lambda' : ℝ) (b c m : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hbc : 2 ≤ b + c) (hm : 2 ≤ m)
    (hctrl : (∑ i ∈ Finset.Icc b m,
        (1 - if omega ∈ goodEvent M none i z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (b : ℝ)))
    (hinfl : lambda * ((m : ℝ) - (b : ℝ)) ≤
      lambda' * ((m : ℝ) - ((b : ℝ) + (c : ℝ)))) :
    (∑ j ∈ Finset.Icc (b + c - 2) (m - 2),
        (1 - if omega ∈ goodEvent M none (j + 2) z epsilon s then (1 : ℝ)
          else 0)) <
      1 + lambda' * (((m - 2 : ℕ) : ℝ) - ((b + c - 2 : ℕ) : ℝ)) := by
  rw [sum_shift_two M epsilon s (b + c) m z omega hbc hm]
  have hcast : ((m - 2 : ℕ) : ℝ) - ((b + c - 2 : ℕ) : ℝ) =
      (m : ℝ) - ((b : ℝ) + (c : ℝ)) := by
    rw [Nat.cast_sub hm, Nat.cast_sub hbc]
    push_cast
    ring
  rw [hcast]
  have hrestrict := failure_row_restrict M epsilon s b c m z omega
  linarith

/-- **The rate inflation is affordable.**  On row 2's range the gap exceeds
twice the raise, so doubling the rate pays for it. -/
theorem inflation_of_gap {lambda : ℝ} {b c m : ℕ} (hlam : 0 ≤ lambda)
    (hgap : 2 * (c : ℝ) ≤ (m : ℝ) - (b : ℝ)) :
    lambda * ((m : ℝ) - (b : ℝ)) ≤
      (2 * lambda) * ((m : ℝ) - ((b : ℝ) + (c : ℝ))) := by
  nlinarith only [hlam, hgap]

/-- The inflated rate still meets the selection's `lambda ≤ 1/2` requirement,
because the ladder constant `C1` is ours to enlarge. -/
theorem inflated_lambda_le_half {C1 alpha : ℝ}
    (hlam : Section6Stopping.holderStoppingLambda C1 alpha ≤ 1 / 4) :
    2 * Section6Stopping.holderStoppingLambda C1 alpha ≤ 1 / 2 := by
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
