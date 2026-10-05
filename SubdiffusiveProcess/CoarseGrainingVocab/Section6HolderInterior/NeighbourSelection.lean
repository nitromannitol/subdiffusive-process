module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneFinalStep

@[expose] public section

/-!
# The good-scale selection at a grid centre

Everything the selection needs is now in place, at the forced parameters
`n_sel = n - 2`, `top_sel = m - 2`:

* the failure row, from the stopped controls via `ShiftedFailureRow`;
* the room, from the `step` margin via `SelectionRoom`.

The output is a scale `j` with `ω ∈ goodEvent M none (j + 2) y ε s`, and
`j + 2 ≥ n`: the good scale sits at or above the base scale, so the energy
descent of `EnergyScaleTransfer` runs in the right direction.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The good scale at a grid centre.** -/
theorem exists_goodScale_at_gridCentre
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C1 C2 alpha : ℝ)
    (step m n k : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (y : Vec d) (hygrid : OnTriadicGrid n y) (hy : y ∈ cube d m)
    (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hlam : Section6Stopping.holderStoppingLambda C1 alpha ≤ 1 / 2)
    (hk : 2 * k + 2 ≤ step + 5) :
    ∃ j : ℕ, n - 2 ≤ j ∧ k ≤ j ∧
      omega ∈ goodEvent M none (j + 2) y
        (Section6Stopping.holderStoppingEpsilon C2 alpha)
        Section6Stopping.holderStoppingS := by
  -- the stopped failure row at the centre
  have hctrl := (Section6Stopping.measurableHolder_stopped_controls_at_parameters
    M C1 C2 alpha step m n omega hstop y hygrid hy).2
  have hfail := shifted_failure_row M
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha) n m y omega hn hm hctrl
  -- the room, from the step margin
  have hgap := gap_ge_step_of_stopping M alpha
    (Section6Stopping.holderStoppingLambda C1 alpha)
    (Section6Stopping.holderStoppingEpsilon C2 alpha) step m n omega hstop
  have hcast : ((m - 2 : ℕ) : ℝ) - ((n - 2 : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    rw [Nat.cast_sub hm, Nat.cast_sub hn]
    push_cast
    ring
  have hroom : (k : ℝ) + 6 +
      Section6Stopping.holderStoppingLambda C1 alpha *
        (((m - 2 : ℕ) : ℝ) - ((n - 2 : ℕ) : ℝ)) ≤
      (((m - 2 : ℕ) : ℝ) - ((n - 2 : ℕ) : ℝ)) + 5 := by
    rw [hcast]
    exact selection_room_of_step hlam hk hgap
  obtain ⟨j, hj1, _hj2, hj3, hgood⟩ :=
    Section6Holder.exists_holderGoodScale_of_failure_bound M
      (Section6Stopping.holderStoppingEpsilon C2 alpha)
      Section6Stopping.holderStoppingS
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (n - 2) (m - 2) k y omega hfail hroom
  exact ⟨j, hj1, hj3, hgood⟩

/-- The selected scale sits at or above the base scale. -/
theorem base_le_selected {n j : ℕ} (hn : 2 ≤ n) (hj : n - 2 ≤ j) :
    n ≤ j + 2 := by omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
