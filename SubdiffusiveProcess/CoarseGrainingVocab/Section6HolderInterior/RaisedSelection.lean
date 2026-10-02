import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RaisedFailureRow

/-!
# The good-scale selection at a raised base

`exists_goodScale_at_gridCentre` runs the selection at the grid scale itself and
returns `j ≥ b - 2`.  The energy gate needs `j ≥ b + 3` (see `RaisedFailureRow`),
so the selection is re-run over the raised index set `Icc (b + c) m`, the failure
row surviving by restriction and the rate inflating from `lambda` to `lambda'`.

The grid scale stays at `b`: the centre `y` is still a point of the *scale-`b`*
triadic grid, which is what makes it available within `3^b` of an arbitrary base
point `x`.  Only the range of scales searched is raised.  With `c = 5` the output
is `j ≥ b + 3`, exactly the gate's centre-proximity threshold.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The good scale at a grid centre, with the base raised by `c`.** -/
theorem exists_goodScale_at_gridCentre_raised
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha lambda' : ℝ)
    (step m b c k : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (y : Vec d) (hygrid : OnTriadicGrid b y) (hy : y ∈ cube d m)
    (hbc : 2 ≤ b + c) (hm : 2 ≤ m)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (b : ℤ))
    (hinfl : Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (b : ℝ)) ≤
      lambda' * ((m : ℝ) - ((b : ℝ) + (c : ℝ))))
    (hroom : (k : ℝ) + 6 + lambda' * ((m : ℝ) - ((b : ℝ) + (c : ℝ))) ≤
      ((m : ℝ) - ((b : ℝ) + (c : ℝ))) + 5) :
    ∃ j : ℕ, b + c - 2 ≤ j ∧ k ≤ j ∧
      omega ∈ goodEvent M none (j + 2) y
        (Section6Stopping.holderStoppingEpsilon C2 alpha)
        Section6Stopping.holderStoppingS := by
  -- the stopped failure row at the centre, at the *grid* scale `b`
  have hctrl := (Section6Stopping.measurableHolder_stopped_controls_at_parameters
    M C1 C2 alpha step m b omega hstop y hygrid hy).2
  -- restrict to the raised range and inflate the rate
  have hfail := raised_failure_row M
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha) lambda'
    b c m y omega hbc hm hctrl hinfl
  have hcast : ((m - 2 : ℕ) : ℝ) - ((b + c - 2 : ℕ) : ℝ) =
      (m : ℝ) - ((b : ℝ) + (c : ℝ)) := by
    rw [Nat.cast_sub hm, Nat.cast_sub hbc]
    push_cast
    ring
  have hroom' : (k : ℝ) + 6 +
      lambda' * (((m - 2 : ℕ) : ℝ) - ((b + c - 2 : ℕ) : ℝ)) ≤
      (((m - 2 : ℕ) : ℝ) - ((b + c - 2 : ℕ) : ℝ)) + 5 := by
    rw [hcast]
    exact hroom
  obtain ⟨j, hj1, _hj2, hj3, hgood⟩ :=
    Section6Holder.exists_holderGoodScale_of_failure_bound M
      (Section6Stopping.holderStoppingEpsilon C2 alpha)
      Section6Stopping.holderStoppingS lambda'
      (b + c - 2) (m - 2) k y omega hfail hroom'
  exact ⟨j, hj1, hj3, hgood⟩

/-- With `c = 5` the selected scale clears the gate's proximity threshold. -/
theorem gate_proximity_of_raised {b j : ℕ} (hj : b + 5 - 2 ≤ j) :
    b + 3 ≤ j := by omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
