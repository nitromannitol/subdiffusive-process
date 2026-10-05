module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.WitnessOffset

@[expose] public section

/-!
# Matching the selection's good event to the energy gate's good event

`exists_interiorHolderProjectedEnergyGate` consumes

```text
  omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8)
```

while `exists_goodScale_at_gridCentre` produces

```text
  omega ∈ goodEvent M (some L) (j + 2) y (holderStoppingEpsilon C2 alpha)
    holderStoppingS .
```

Two parameters must be reconciled, and **both are pinned, not estimated**:

* the fractional order.  `holderStoppingS = 1/32` is a hard-coded manuscript
  constant, so the gate's `sOrder.1 / 8` matches it only at `sOrder.1 = 1/4` —
  which is exactly the **top** of the gate's admissible window
  `Set.Icc (512 * M.delta ^ 2) (1 / 4)`.  There is therefore no freedom here:
  the interior branch must be run at `s = 1/4`, and the window is nonempty only
  when `512 * M.delta ^ 2 ≤ 1/4`.  That is a smallness condition on the model,
  and it is affordable because the frozen anchor guards everything behind
  `M.delta ≤ C⁻¹` with `C` existentially ours: `C ≥ 46` suffices.

* the amplitude.  `goodEvent` is monotone in its amplitude on `[0,1]`
  (`goodEvent_subset_one`), so the selection's `epsilon` upgrades to the gate's
  `1` as soon as `holderStoppingEpsilon C2 alpha ≤ 1`, which the ladder constant
  `C2 ≥ 1` supplies for every `alpha ≥ 1/2`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}
variable {L : ℕ}

/-- The fractional order forced on the interior branch: the unique value whose
eighth is the manuscript's `holderStoppingS`. -/
def interiorFractionalOrder_cut : FractionalOrder := ⟨1 / 4, by norm_num⟩

@[simp] theorem interiorFractionalOrder_val :
    (interiorFractionalOrder_cut).1 = 1 / 4 := rfl

/-- **The gate's fractional parameter is the stopping tree's `s`.**  This is an
equality, not an estimate: `1/4` is the only admissible order that matches. -/
theorem interiorFractionalOrder_div_eight_cut :
    (interiorFractionalOrder_cut).1 / 8 = Section6Stopping.holderStoppingS := by
  norm_num [interiorFractionalOrder_cut, Section6Stopping.holderStoppingS]

/-- **`delta ≤ C⁻¹` with `C ≥ 46` puts the forced order inside the gate's
window.**  The gate needs `sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1/4)`, and at
the forced order this is exactly `512 * M.delta ^ 2 ≤ 1/4`. -/
theorem interiorFractionalOrder_mem_window_cut
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C : ℝ} (hC : 46 ≤ C)
    (hdelta0 : 0 ≤ M.delta) (hdelta : M.delta ≤ C⁻¹) :
    (interiorFractionalOrder_cut).1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) := by
  have hC0 : (0 : ℝ) < C := by linarith
  have hinv : C⁻¹ ≤ (46 : ℝ)⁻¹ := by
    exact inv_anti₀ (by norm_num) hC
  have hd : M.delta ≤ (46 : ℝ)⁻¹ := hdelta.trans hinv
  have hsq : M.delta ^ 2 ≤ ((46 : ℝ)⁻¹) ^ 2 := by
    exact pow_le_pow_left₀ hdelta0 hd 2
  refine ⟨?_, le_rfl⟩
  rw [interiorFractionalOrder_val]
  nlinarith only [hsq]

/-- The manuscript amplitude is nonnegative. -/
theorem holderStoppingEpsilon_nonneg_cut {C2 alpha : ℝ} (hC2 : 0 ≤ C2) :
    0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha := by
  have : (0 : ℝ) ≤ Real.sqrt (1 - alpha) := Real.sqrt_nonneg _
  have hinv : (0 : ℝ) ≤ C2⁻¹ := inv_nonneg.2 hC2
  exact mul_nonneg hinv this

/-- **The manuscript amplitude is at most one** for every `alpha ≥ 1/2`,
provided the ladder constant `C2` is at least one.  No upper bound on `alpha` is
needed: past `alpha = 1` the square root is zero. -/
theorem holderStoppingEpsilon_le_one_cut {C2 alpha : ℝ} (hC2 : 1 ≤ C2)
    (halpha0 : 1 / 2 ≤ alpha) :
    Section6Stopping.holderStoppingEpsilon C2 alpha ≤ 1 := by
  have hC20 : (0 : ℝ) < C2 := by linarith
  have hinv : C2⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hC2
  have hle : Real.sqrt (1 - alpha) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) - alpha ≤ 1 by linarith)
    simpa using h
  have hnn : (0 : ℝ) ≤ Real.sqrt (1 - alpha) := Real.sqrt_nonneg _
  have hinv0 : (0 : ℝ) ≤ C2⁻¹ := inv_nonneg.2 hC20.le
  calc Section6Stopping.holderStoppingEpsilon C2 alpha
      = C2⁻¹ * Real.sqrt (1 - alpha) := rfl
    _ ≤ 1 * 1 := by
        exact mul_le_mul hinv hle hnn (by norm_num)
    _ = 1 := by ring

/-- **The selection's good event feeds the energy gate.**  Amplitude upgraded by
`goodEvent_subset_one`, fractional parameter matched exactly. -/
theorem goodEvent_gate_of_selection_cut
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C2 alpha : ℝ} (hC2 : 1 ≤ C2)
    (halpha0 : 1 / 2 ≤ alpha) (j : ℕ) (y : Vec d)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hgood : omega ∈ goodEvent M (some L) (j + 2) y
      (Section6Stopping.holderStoppingEpsilon C2 alpha)
      Section6Stopping.holderStoppingS) :
    omega ∈ goodEvent M (some L) (j + 2) y 1
      ((interiorFractionalOrder_cut).1 / 8) := by
  rw [interiorFractionalOrder_div_eight_cut]
  exact goodEvent_subset_one M (some L) (j + 2) y
    (holderStoppingEpsilon_nonneg_cut (by linarith))
    (holderStoppingEpsilon_le_one_cut hC2 halpha0) hgood

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
