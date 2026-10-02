import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ShiftedFailureRow

/-!
# The good-scale selection's room condition, and what it costs

At the forced parameters of Addendum 18 (`n_sel = n-2`, `top_sel = m-2`, so
`top_sel - n_sel = m - n`) the selection's room hypothesis

```text
  (k : ℝ) + 6 + λ·(top - n)  ≤  (top : ℝ) - n + 5
```

reads `(k : ℝ) + 1 ≤ (1 - λ)·(m - n)`, and with `λ ≤ 1/2` it is implied by

```text
  m - n  ≥  2k + 2 .
```

**This is a genuine constraint on the `step` margin.**  The only source of a
lower bound on `m - n` is the frozen hypothesis `X ≤ m - n` together with
`X ≥ step + 5` (the stopping scale is `max(depths) + step + 5` by construction).
So the selection needs

```text
  2k + 2  ≤  step + 5 ,
```

i.e. `step ≥ 2k - 3`.  In particular **`step = 0` is not admissible** once
`k ≥ 2`, and `k` comes from `exists_holderContractionParameters`, where it is
`max N 4 ≥ 4`.  Row 1 was instantiated at `step = 0` (Addendum 7); the row
packages must therefore be run at a `step` large enough for the selection, and
row 1 re-read there.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- The stopping scale is at least `step + 5`. -/
theorem step_add_five_le_measurableHolderStoppingScale
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    step + 5 ≤ Section6Stopping.measurableHolderStoppingScale M alpha lambda
      epsilon step m omega := by
  have heq := Section6Stopping.holderStoppingScale_eq_max_depth_add
    M alpha lambda epsilon step m omega
  have hle := Section6Stopping.holderStoppingScale_le_measurable
    M alpha lambda epsilon step m omega
  omega

/-- The frozen stopping hypothesis gives `m - n ≥ step + 5`. -/
theorem gap_ge_step_of_stopping
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha lambda
        epsilon step m omega : ℤ) ≤ (m : ℤ) - (n : ℤ)) :
    ((step : ℤ) + 5) ≤ (m : ℤ) - (n : ℤ) := by
  have h := step_add_five_le_measurableHolderStoppingScale M alpha lambda epsilon
    step m omega
  omega

/-- **The room condition, from the step margin.**  With `λ ≤ 1/2` and
`2k + 2 ≤ step + 5`, the frozen stopping hypothesis supplies the selection's
room. -/
theorem selection_room_of_step {k step m n : ℕ} {lambda : ℝ}
    (hlam : lambda ≤ 1 / 2)
    (hk : 2 * k + 2 ≤ step + 5)
    (hgap : ((step : ℤ) + 5) ≤ (m : ℤ) - (n : ℤ)) :
    (k : ℝ) + 6 + lambda * ((m : ℝ) - (n : ℝ)) ≤ ((m : ℝ) - (n : ℝ)) + 5 := by
  have hgapR : ((step : ℝ) + 5) ≤ (m : ℝ) - (n : ℝ) := by
    have : ((step : ℤ) + 5 : ℤ) ≤ ((m : ℤ) - (n : ℤ)) := hgap
    have hc : (((step : ℤ) + 5 : ℤ) : ℝ) ≤ (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast this
    push_cast at hc
    linarith
  have hkR : 2 * (k : ℝ) + 2 ≤ (step : ℝ) + 5 := by exact_mod_cast hk
  have hgapBig : 2 * (k : ℝ) + 2 ≤ (m : ℝ) - (n : ℝ) := by linarith
  have hgap0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have : (0 : ℝ) ≤ 2 * (k : ℝ) + 2 := by positivity
    linarith
  have hhalf : lambda * ((m : ℝ) - (n : ℝ)) ≤ (1 / 2) * ((m : ℝ) - (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hlam hgap0
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
