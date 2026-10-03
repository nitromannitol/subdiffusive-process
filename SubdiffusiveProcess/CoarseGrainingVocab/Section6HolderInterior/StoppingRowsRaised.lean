module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CampanatoFamily

@[expose] public section

/-!
# Raising the stopping base, once, for every consumer

`exists_interiorHolderCampanatoFull` and `exists_interiorHolderIterationApplied`
have **identical** stopping interfaces: a centre `z ∈ cube d (domain - 1)` with
no grid condition, and two rows read over `Finset.Icc n domain`, where `n` is
also the lower window scale.  Both are therefore the printed estimates with the
window pinned to the base only through those two rows.

Raising the base from `n` to `n'` is the same two-line argument in both cases, so
it is factored out here rather than restating either conclusion.  A consumer that
wants the printed family at window `n'` applies the landed theorem at `n'` and
`lambda'`, discharging its two stopping hypotheses with `stopping_rows_raised`.

This is what `exists_interiorCampanatoFamily` does for the oscillation row; row
3's long branch does the same with the excess row of
`exists_interiorHolderIterationApplied`, whose conclusion is not restated here
precisely so that nothing is duplicated by hand.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **Both stopping rows, raised from base `n` to base `n'`.**

The rows restrict because every summand is nonnegative; they still meet the
*smaller* bound at the raised base because of the rate inflation `hinfl`, which
`RaisedFailureRow.inflation_of_gap` supplies with `lambda' = 2 * lambda` whenever
`2 * (n' - n) ≤ domain - n`. -/
theorem stopping_rows_raised (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (epsilon lambda lambda' : ℝ) (n n' domain : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hnn : n ≤ n')
    (herr : (∑ i ∈ Finset.Icc n domain,
        accumulatedError M none i z Section6Stopping.holderStoppingS omega) ≤
      lambda * ((domain : ℝ) - (n : ℝ)))
    (hfail : (∑ i ∈ Finset.Icc n domain,
        ((1 : ℝ) - if omega ∈ goodEvent M none i z epsilon
          Section6Stopping.holderStoppingS then 1 else 0)) <
      1 + lambda * ((domain : ℝ) - (n : ℝ)))
    (hinfl : lambda * ((domain : ℝ) - (n : ℝ)) ≤
      lambda' * ((domain : ℝ) - (n' : ℝ))) :
    (∑ i ∈ Finset.Icc n' domain,
        accumulatedError M none i z Section6Stopping.holderStoppingS omega) ≤
      lambda' * ((domain : ℝ) - (n' : ℝ)) ∧
    (∑ i ∈ Finset.Icc n' domain,
        ((1 : ℝ) - if omega ∈ goodEvent M none i z epsilon
          Section6Stopping.holderStoppingS then 1 else 0)) <
      1 + lambda' * ((domain : ℝ) - (n' : ℝ)) := by
  constructor
  · exact le_trans
      (accumulatedError_row_restrict M Section6Stopping.holderStoppingS
        n n' domain z omega hnn)
      (le_trans herr hinfl)
  · have hrestrict := failure_row_restrict M epsilon
      Section6Stopping.holderStoppingS n (n' - n) domain z omega
    rw [show n + (n' - n) = n' by omega] at hrestrict
    linarith

/-- The inflation hypothesis in the form row 2 and row 3 both meet: on their
range the gap exceeds twice the raise, so doubling the rate pays for it. -/
theorem stopping_inflation_of_gap {lambda : ℝ} {n n' domain : ℕ}
    (hlam : 0 ≤ lambda) (hnn : n ≤ n')
    (hgap : 2 * ((n' : ℝ) - (n : ℝ)) ≤ (domain : ℝ) - (n : ℝ)) :
    lambda * ((domain : ℝ) - (n : ℝ)) ≤
      (2 * lambda) * ((domain : ℝ) - (n' : ℝ)) := by
  have hnn' : (n : ℝ) ≤ (n' : ℝ) := by exact_mod_cast hnn
  nlinarith only [hlam, hgap, hnn']

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
