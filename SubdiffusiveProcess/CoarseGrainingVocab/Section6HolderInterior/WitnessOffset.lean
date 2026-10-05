module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GammaOneComposition
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.NeighbourSelection

@[expose] public section

/-!
# Offsetting the witness, and why row 2 needs it

Step 6 ties its conclusion scale to its good-event scale by a **fixed offset of
six**: the good event is at `n + 2` and the conclusion at `n - 4`
(`EnergyCoverGate`).  The selection, by contrast, only pins the good-event scale
to a *range* starting at the control's base.  So to place Step 6's
conclusion at or above row 2's scale `n`, the selection must be run at base
`n + 4`, which needs the stopped control at starting scale `n + 6`, i.e.

```text
  X ≤ m - n - 6 ,
```

whereas the hypothesis supplies only `X ≤ m - n`.  **The shortfall is
exactly six**, and it is not recoverable from the `step` margin: `X ≥ step + 5`
bounds `X` from below, not above.

The fix is available because the witness `X` is *ours to choose*: taking
`X := stoppingScale + 6` makes the hypothesis `X ≤ m - n` say
`stoppingScale ≤ m - n - 6`, exactly what the selection needs.  Measurability
and positivity are immediate, and the Γ₁ tail survives because a constant shift
of the threshold is absorbed by enlarging the constant — proved here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **A constant shift of the threshold is absorbed by enlarging the constant.**
-/
theorem gammaOneRHS_offset (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {C C' alpha : ℝ} {c k : ℕ} (hC : 0 < C) (hck : c ≤ k)
    (hCC' : C + (c : ℝ) ≤ C') :
    gammaOneRHS M C alpha (k - c) ≤ gammaOneRHS M C' alpha k := by
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hC' : 0 < C' := by linarith
  have hDnn : (0 : ℝ) ≤ M.delta ^ 2 * |Real.log M.delta| := by positivity
  have hkc : ((k - c : ℕ) : ℝ) = (k : ℝ) - (c : ℝ) := by
    rw [Nat.cast_sub hck]
  rcases eq_or_lt_of_le hDnn with hD0 | hD
  · rw [gammaOneRHS_eq, gammaOneRHS_eq, ← hD0]
    simp only [mul_zero, div_zero, neg_zero, Real.exp_zero, mul_one]
    linarith
  · have hW : max ((k : ℝ) - C') 0 ≤ max (((k - c : ℕ) : ℝ) - C) 0 := by
      refine max_le_max ?_ le_rfl
      rw [hkc]
      linarith
    have hexp : (1 - alpha) ^ 2 * max ((k : ℝ) - C') 0 /
        (C' * (M.delta ^ 2 * |Real.log M.delta|)) ≤
          (1 - alpha) ^ 2 * max (((k - c : ℕ) : ℝ) - C) 0 /
            (C * (M.delta ^ 2 * |Real.log M.delta|)) :=
      gammaOne_exponent_le hC' hC hD (by linarith) hW
    rw [gammaOneRHS_eq, gammaOneRHS_eq]
    exact exp_bound_le hC.le (by linarith) hexp

/-- The offset witness is measurable and positive. -/
theorem offsetWitness_measurable_pos
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m c : ℕ) :
    Measurable (fun ω => Section6Stopping.measurableHolderStoppingScale M alpha
        lambda epsilon step m ω + c) ∧
      ∀ ω, 0 < Section6Stopping.measurableHolderStoppingScale M alpha lambda
        epsilon step m ω + c := by
  refine ⟨(Section6Stopping.measurable_measurableHolderStoppingScale M alpha
      lambda epsilon step m).add_const c, fun ω => ?_⟩
  have := Section6Stopping.measurableHolderStoppingScale_pos M alpha lambda
    epsilon step m ω
  omega

/-- The offset witness's hypothesis is the un-offset scale with room. -/
theorem stopping_of_offsetWitness
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n c : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hstop : ((Section6Stopping.measurableHolderStoppingScale M alpha lambda
        epsilon step m omega + c : ℕ) : ℤ) ≤ (m : ℤ) - (n : ℤ)) :
    (Section6Stopping.measurableHolderStoppingScale M alpha lambda epsilon
      step m omega : ℤ) ≤ (m : ℤ) - ((n + c : ℕ) : ℤ) := by
  push_cast at hstop ⊢
  omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
