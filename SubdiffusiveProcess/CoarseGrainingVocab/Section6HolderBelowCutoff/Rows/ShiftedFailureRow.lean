module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.GoodScaleSelection
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.Geometry

@[expose] public section

/-!
# The stopped failure row in the shape the good-scale selection consumes

`Section6Holder.exists_holderGoodScale_of_failure_bound` wants the failure row
over `Finset.Icc n top` with the good event evaluated at `j + 2`, and bounded by
`1 + λ·(top - n)`.  The stopped controls
(`Section6Stopping.measurableHolder_stopped_controls_at_parameters`) give it over
`Finset.Icc n m` with the event at `j`, bounded by `1 + λ·(m - n)`.

The two match **exactly** — but only at the right parameters.  Running the
selection at `n_sel = n - 2`, `top_sel = m - 2` turns its index set into

```text
  {j + 2 : j ∈ Icc (n-2) (m-2)} = Icc n m ,
```

and its bound into `1 + λ·((m-2) - (n-2)) = 1 + λ·(m - n)`: the control's own
bound, with nothing to spare.  Any other choice of `top` leaves a gap of the
wrong sign, since the control's `1 + λ(m-n)` exceeds the required
`1 + λ(top-n)` whenever `top < m`.

The selected good scale is then `j + 2 ∈ [n, n + card]`, i.e. at or *above*
row 2's scale — which is why the descent of `EnergyScaleTransfer` is the right
direction.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}
variable {L : ℕ}

/-- The shift `j ↦ j + 2` carries `Icc (n-2) (m-2)` onto `Icc n m`. -/
theorem sum_shift_two_cut (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s : ℝ)
    (n m : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∑ j ∈ Finset.Icc (n - 2) (m - 2),
        (1 - if omega ∈ goodEvent M (some L) (j + 2) z epsilon s then (1 : ℝ) else 0))
      = ∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) i z epsilon s then (1 : ℝ) else 0) := by
  refine Finset.sum_nbij' (fun j => j + 2) (fun i => i - 2) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    show j + 2 - 2 = j
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    show i - 2 + 2 = i
    omega
  · intro j _
    rfl

/-- **The failure row at the selection's parameters.**  The stopped control's
bound is *exactly* what the selection needs at `n_sel = n-2`, `top_sel = m-2`. -/
theorem shifted_failure_row_cut (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (epsilon s lambda : ℝ) (n m : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hctrl : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) i z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ))) :
    (∑ j ∈ Finset.Icc (n - 2) (m - 2),
        (1 - if omega ∈ goodEvent M (some L) (j + 2) z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * (((m - 2 : ℕ) : ℝ) - ((n - 2 : ℕ) : ℝ)) := by
  rw [sum_shift_two_cut M epsilon s n m z omega hn hm]
  have hcast : ((m - 2 : ℕ) : ℝ) - ((n - 2 : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    rw [Nat.cast_sub hm, Nat.cast_sub hn]
    push_cast
    ring
  rw [hcast]
  exact hctrl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
