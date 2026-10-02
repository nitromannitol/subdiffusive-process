import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowThreeArithmetic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.IterationFamilies
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.IterationApplied
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.IterationFamilies
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.RecurrenceBudget

/-!
# The `R` hypothesis of the iteration's excess row

The excess conjunct of `exists_interiorHolderIterationApplied_cut` is stated for any
`R` with `epsRow j ≤ R` on the index range.  Unfolding,

```text
  holderRecurrenceEpsilon_cut L K M epsilon s j z omega
    = K * min epsilon (delta^2 + epsilon^8 + accumulatedError ...)
        * (indicator of the good event) ,
```

so the row is bounded by `K * epsilon` **outright** — the `min` gives `epsilon`
and the indicator is at most one, with no appeal to the good-event structure and
no hypothesis beyond nonnegativity of `K` and `epsilon`.

This is what supplies row 3's oscillation coefficient: with the manuscript's
`epsilon = holderStoppingEpsilon C2 alpha = C2⁻¹ sqrt (1 - alpha)`, the bound
`R = K * epsilon` carries exactly the `sqrt (1 - alpha)` that the frozen row-3
coefficient `C * sqrt (1 - alpha) * 3 ^ (-ell)` requires.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}
variable {L : ℕ}

/-- The concrete recurrence row is bounded by `K * epsilon`. -/
theorem holderRecurrenceEpsilon_le_const_cut {K : ℝ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {epsilon s : ℝ} (j : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hK : 0 ≤ K) (heps : 0 ≤ epsilon) :
    holderRecurrenceEpsilon_cut L K M epsilon s j z omega ≤ K * epsilon := by
  unfold holderRecurrenceEpsilon_cut
  have hmin : min epsilon
      (M.delta ^ 2 + epsilon ^ 8 +
        accumulatedError M (some L) (j + 2) z s omega) ≤ epsilon := min_le_left _ _
  have hmin0 : 0 ≤ min epsilon
      (M.delta ^ 2 + epsilon ^ 8 +
        accumulatedError M (some L) (j + 2) z s omega) := by
    refine le_min heps ?_
    have := accumulatedError_nonneg M (some L) s (j + 2) z omega
    positivity
  by_cases hgood : omega ∈ goodEvent M (some L) (j + 2) z epsilon s
  · rw [if_pos hgood, mul_one]
    exact mul_le_mul_of_nonneg_left hmin hK
  · rw [if_neg hgood, mul_zero]
    positivity

/-- **The `R` hypothesis, discharged uniformly in `j`.** -/
theorem holderIterationEpsilon_le_const_cut {K : ℝ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {epsilon s : ℝ} (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (j : ℤ)
    (hK : 0 ≤ K) (heps : 0 ≤ epsilon) :
    holderIterationEpsilon_cut L K M epsilon s z omega j ≤ K * epsilon := by
  unfold holderIterationEpsilon_cut
  by_cases hj : 0 ≤ j
  · rw [if_pos hj]
    exact holderRecurrenceEpsilon_le_const_cut M j.toNat z omega hK heps
  · rw [if_neg hj]
    positivity

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
