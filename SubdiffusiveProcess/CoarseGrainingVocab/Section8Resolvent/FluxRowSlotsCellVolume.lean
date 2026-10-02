/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsEnergy
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszRepairedInstantiation




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ## 1. The identity -/

/-- **The flux-row partition's cell volume is the enlargement's volume.**

`3^{d(m+1)} = 3^d · 3^{dm}`, i.e. the partition's `|Q|` exceeds the
normalization of `localSymmetricEnergyENorm (originCube d m)` by the
dimension-only factor `3^d`. -/
theorem volume_translatedCube_succ_toReal_eq_three_pow_mul_cubeVolume
    (m : ℤ) (z : Vec d) :
    (volume (translatedCube d (m + 1) z)).toReal =
      (3 : ℝ) ^ d * cubeVolume (originCube d m) := by
  rw [Section6BoundedMultiplier.volume_translatedCube_toReal, cubeVolume,
    cubeScaleFactor_originCube, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), mul_pow]
  ring

/-- The repaired flux-row partition's cell volume, in the origin-cube
normalization consumed by `localSymmetricEnergyENorm`. -/
theorem repairedFluxRowRieszPartition_cellVolume_eq [NeZero d]
    {base : ℤ} {failure : TriadicCube d → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)}
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (q : RefinedStoppingCell failure omega base) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q =
      (3 : ℝ) ^ d * cubeVolume (originCube d (refinedStoppingScale q)) :=
  volume_translatedCube_succ_toReal_eq_three_pow_mul_cubeVolume _ _

/-! ## 2. The Caccioppoli in the consumer's normalization -/

/-- The Caccioppoli bound stated with the *origin-cube* volume becomes the same
bound with the *partition's* cell volume, at the cost of the dimension-only
factor `3^d` on the constant. -/
theorem fluxRowSlots_enlargedCaccioppoli_of_cubeVolume
    {S0 Cc mass V : ℝ} {W : ℝ}
    (hV : V = (3 : ℝ) ^ d * W)
    (hcacc : W * S0 ^ 2 ≤ Cc * mass) :
    V * S0 ^ 2 ≤ ((3 : ℝ) ^ d * Cc) * mass := by
  subst hV
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  calc (3 : ℝ) ^ d * W * S0 ^ 2 = (3 : ℝ) ^ d * (W * S0 ^ 2) := by ring
    _ ≤ (3 : ℝ) ^ d * (Cc * mass) := mul_le_mul_of_nonneg_left hcacc h3
    _ = ((3 : ℝ) ^ d * Cc) * mass := by ring

/-- The smallness budget with the enlargement factor made explicit: it is the
budget of `fluxRowSlots_energy_budget_of_smallness` for the constant
`3^d · Cc`. -/
theorem fluxRowSlots_three_pow_budget_of_smallness
    {alpha t R sigma cellSize K Cc lambdaInv : ℝ}
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRS : R ≤ cellSize)
    (hsmall : K ^ 2 * ((3 : ℝ) ^ d * Cc) ≤ t⁻¹ * Real.rpow R (2 * sigma)) :
    alpha * K ^ 2 * ((3 : ℝ) ^ d * Cc) ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) *
        (1 + (alpha * lambdaInv) ^ 2) :=
  fluxRowSlots_energy_budget_of_smallness (d := d) (lambdaInv := lambdaInv)
    halpha ht hR hRS hsmall

/-! ## 3. The energy slot in the consumer's normalization -/

/-- **The energy slot with `V := cellVolume q`.**

Identical to `fluxRowSlots_energy_slot_of_inputs` except that the Caccioppoli
input is supplied in the origin-cube normalization (`cubeVolume`), which is the
normalization of `localSymmetricEnergyENorm` and hence the shape in which
`wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le` delivers it,
while the conclusion is stated with the partition's own `cellVolume`.  The
`3^d` is paid once, in the budget. -/
theorem fluxRowSlots_energy_slot_enlarged_of_inputs
    {alpha t R sigma fEnergy theta cellSize S S0 K Cc mass lambdaInv V W : ℝ}
    {graphDistance : ℕ}
    (halpha : 0 < alpha) (hW : 0 ≤ W) (hS : 0 ≤ S) (hCc : 0 ≤ Cc)
    (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hVW : V = (3 : ℝ) ^ d * W)
    (hSle : S ≤ K * S0)
    (hcacc : W * S0 ^ 2 ≤ Cc * mass)
    (hmass : mass ≤ Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)
    (hbudget : alpha * K ^ 2 * ((3 : ℝ) ^ d * Cc) ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) *
        (1 + (alpha * lambdaInv) ^ 2)) :
    V * (Real.sqrt alpha * S) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
          graphDistance d * (1 + (alpha * lambdaInv) ^ 2) := by
  refine fluxRowSlots_energy_slot_of_inputs (Cc := (3 : ℝ) ^ d * Cc) halpha ?_ hS
    ?_ hfEnergy htheta hSle
    (fluxRowSlots_enlargedCaccioppoli_of_cubeVolume hVW hcacc) hmass hbudget
  · rw [hVW]; positivity
  · positivity

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
