import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RaisedSelection

/-!
# The descent price, and why it is gap-uniform

Row 2 is assembled at the **grid centres**: for a neighbour `y` of the off-grid
base point `x`, the energy gate is applied with the good-event centre and the
window base point *both* equal to `y`.  The gate's proximity condition
`y ∈ truncatedCube d m (n_gate - 3) y` is then trivially satisfied, so the
obstruction recorded in `RaisedFailureRow` never has to be paid: the off-grid
point is reached by the **energy cover**, not by the gate's proximity slack.

What the raise is still needed for is scale arithmetic.  The gate's conclusion
sits at `j - 4` where `j` is the selected scale, and the cover consumes it at the
cover scale `n`; since `vectorNormalizedL2On_scaleTransfer` runs from the smaller
window to the larger, the gate's conclusion must sit at or above `n`, i.e.
`j ≥ n + 4`.  Raising the selection's base by `c = 6` at grid scale `b = n`
delivers exactly `j ≥ b + c - 2 = n + 4`.

The descent from `j - 4` down to `n` costs `scaleTransferPrice d (j - 4 - n)`,
and `j` is *not* bounded by a constant: the selection only gives

```text
  j ≤ base + (holderBadNatScales ...).card ,   card < k + 1 + lambda' * (top - base) ,
```

so the price grows like `3 ^ (lambda' * (m - n) * d / 2)` — it **depends on the
gap**.  This is the same shape as the ladder exponential of Addendum 3, and it is
absorbed the same way: `lambda = C1⁻¹ (1 - alpha)` and `lambda' = 2 * lambda`, so

```text
  lambda' * d = 2 * d * (1 - alpha) / C1 ≤ (1 - alpha) / 2   as soon as   C1 ≥ 4 * d ,
```

leaving the price below `3 ^ ((1 - alpha) * (m - n) / 2)` — **half** of row 2's
own budget `3 ^ ((1 - alpha) * (m - n))`, with the other half left for the legs.
So the descent is gap-uniform provided the ladder constant is taken at least
`4 * d`.  That is a *dimension-dependent* lower bound on `C1`; it is recorded in
the constant table of the report.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The raised selection, retaining the upper bound on the selected scale.**
The upper bound is what makes the descent price estimable at all. -/
theorem exists_goodScale_at_gridCentre_raised_bounded
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
    ∃ j : ℕ, b + c - 2 ≤ j ∧
      ((j : ℝ) ≤ ((b + c - 2 : ℕ) : ℝ) +
        ((Section6Holder.holderBadNatScales M
            (Section6Stopping.holderStoppingEpsilon C2 alpha)
            Section6Stopping.holderStoppingS
            (b + c - 2) (m - 2) k y omega).card : ℝ)) ∧
      k ≤ j ∧
      omega ∈ goodEvent M none (j + 2) y
        (Section6Stopping.holderStoppingEpsilon C2 alpha)
        Section6Stopping.holderStoppingS := by
  have hctrl := (Section6Stopping.measurableHolder_stopped_controls_at_parameters
    M C1 C2 alpha step m b omega hstop y hygrid hy).2
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
    rw [hcast]; exact hroom
  obtain ⟨j, hj1, hj2, hj3, hgood⟩ :=
    Section6Holder.exists_holderGoodScale_of_failure_bound M
      (Section6Stopping.holderStoppingEpsilon C2 alpha)
      Section6Stopping.holderStoppingS lambda'
      (b + c - 2) (m - 2) k y omega hfail hroom'
  exact ⟨j, hj1, by exact_mod_cast hj2, hj3, hgood⟩

/-- The transfer price in closed rpow form. -/
theorem scaleTransferPrice_eq_rpow (d : ℕ) (gap : ℤ) :
    scaleTransferPrice d gap =
      (3 : ℝ) ^ ((((gap : ℝ) + 2) * (d : ℝ)) / 2) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  unfold scaleTransferPrice
  have hpow : (((3 : ℝ) ^ (gap + 2)) ^ d) =
      (3 : ℝ) ^ ((((gap : ℝ) + 2) * (d : ℝ))) := by
    rw [← Real.rpow_intCast (3 : ℝ) (gap + 2), ← Real.rpow_natCast
      ((3 : ℝ) ^ (((gap : ℤ) + 2 : ℤ) : ℝ)) d, ← Real.rpow_mul h3.le]
    push_cast
    ring_nf
  rw [hpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h3.le]
  ring_nf

/-- **The descent price is gap-uniform once `C1 ≥ 4 * d`.**

`hgap` is the selection's upper bound on the descent, `hlam` is the ladder
condition `lambda' * d ≤ (1 - alpha) / 2`, and the conclusion splits the price
into a constant depending only on `d` and `k` and *half* of row 2's own gap
budget. -/
theorem descent_price_le (d k : ℕ) {alpha lambda' gapR : ℝ} {gap : ℤ}
    (hgapR : 0 ≤ gapR)
    (hgap : (gap : ℝ) ≤ (k : ℝ) + 1 + lambda' * gapR)
    (hlam : lambda' * (d : ℝ) ≤ (1 - alpha) / 2) :
    scaleTransferPrice d gap ≤
      (3 : ℝ) ^ ((((k : ℝ) + 3) * (d : ℝ)) / 2) *
        (3 : ℝ) ^ ((1 - alpha) * gapR / 4) := by
  rw [scaleTransferPrice_eq_rpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h1 : ((gap : ℝ) + 2) * (d : ℝ) ≤
      ((k : ℝ) + 3 + lambda' * gapR) * (d : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hd
  have h3 : (lambda' * (d : ℝ)) * gapR ≤ ((1 - alpha) / 2) * gapR :=
    mul_le_mul_of_nonneg_right hlam hgapR
  nlinarith only [h1, h3]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
