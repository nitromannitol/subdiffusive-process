import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneWindows
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.SelectionRoom
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.CutoffHolderScale

/-!
# The window inputs of the rows, at the cutoff stopping carrier

`Section6HolderInterior.{RowOneWindows, SelectionRoom, RowOneGate}` read three
purely arithmetic facts off the *uncut* stopping carrier
`Section6Stopping.measurableHolderStoppingScale`:

* it is at least `5` (so a frozen stopping hypothesis puts the base point five
  scales inside the cube);
* it is at least `step + 5` (the deterministic room for row 2's good-scale
  selections);
* the hypothesis at `n` transports to any `ell ≤ n`.

All three are consequences of one structural identity — the stopping scale is
`max(error depth, good depth) + step + 5` — which the cutoff carrier satisfies
verbatim (`Section6Stopping.cutoffHolderStoppingScale_eq_max_depth_add`).  This
module states the three facts at `measurableCutoffHolderStoppingScale`.

They are *not* interchangeable with the uncut ones: both carriers are hulls of
choice-defined stopping indices, so a cutoff hypothesis does not unify with an
uncut statement.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The cutoff stopping scale never drops below `5`.** -/
theorem five_le_measurableCutoffHolderStoppingScale
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    5 ≤ Section6Stopping.measurableCutoffHolderStoppingScale M L alpha lambda
      epsilon step m omega := by
  have heq := Section6Stopping.cutoffHolderStoppingScale_eq_max_depth_add
    M L alpha lambda epsilon step m omega
  have hle := Section6Stopping.cutoffHolderStoppingScale_le_measurable
    M L alpha lambda epsilon step m omega
  omega

/-- **The cutoff stopping scale is at least `step + 5`.** -/
theorem step_add_five_le_measurableCutoffHolderStoppingScale
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    step + 5 ≤ Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
      lambda epsilon step m omega := by
  have heq := Section6Stopping.cutoffHolderStoppingScale_eq_max_depth_add
    M L alpha lambda epsilon step m omega
  have hle := Section6Stopping.cutoffHolderStoppingScale_le_measurable
    M L alpha lambda epsilon step m omega
  omega

/-- The frozen cutoff stopping hypothesis puts the base point five scales
inside. -/
theorem base_scale_le_of_stopping_cut {L : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        lambda epsilon step m omega : ℤ) ≤ (m : ℤ) - (n : ℤ)) :
    (n : ℤ) ≤ (m : ℤ) - 5 := by
  have h5 := five_le_measurableCutoffHolderStoppingScale M L alpha lambda epsilon
    step m omega
  omega

/-- The frozen cutoff stopping hypothesis gives `m - n ≥ step + 5`. -/
theorem gap_ge_step_of_stopping_cut {L : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        lambda epsilon step m omega : ℤ) ≤ (m : ℤ) - (n : ℤ)) :
    ((step : ℤ) + 5) ≤ (m : ℤ) - (n : ℤ) := by
  have h := step_add_five_le_measurableCutoffHolderStoppingScale M L alpha lambda
    epsilon step m omega
  omega

/-- The stopped controls needed at the base scale follow from the frozen cutoff
hypothesis at the larger scale. -/
theorem rowOne_stopping_at_base_cut {L : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n ell : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        lambda epsilon step m omega : ℤ) ≤ (m : ℤ) - (n : ℤ))
    (hell : ell ≤ n) :
    (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha lambda
      epsilon step m omega : ℤ) ≤ (m : ℤ) - (ell : ℤ) := by
  have : (ell : ℤ) ≤ (n : ℤ) := by exact_mod_cast hell
  omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
