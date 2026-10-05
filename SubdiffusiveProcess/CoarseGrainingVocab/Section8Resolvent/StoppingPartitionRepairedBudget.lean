module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionHalfGridRefinement

@[expose] public section

/-!
# The stopping rule's scale bounds for the flux row

## The crude-`Λ` budget, RETIRED

This file used to state and produce

```text
RepairedStoppingTSmallnessBudget failure omega base K Lambda t R sigma :
  ∀ q, K² · 4096 · d · Λ · 3^{-2 · scale q} ≤ t⁻¹ R^{2σ}
```

— the flux row's cutoff-multiplier cost along the *crude*-`Λ` Caccioppoli
route, with a single uniform ceiling `Lambda` for every selected cell — together
with `repairedStoppingTSmallnessBudget_of_base`, which produced it from the
same inequality at the base scale.

Both are **deleted**.  The condition is unfillable for the repaired family:

* the flux row no longer takes that route.  `FluxRowSlotsGrowthRatio.lean`
  refutes the geometric discharge (`fluxRowSlotsGrowthRatioBound` already fails
  in the failure-free environment, where the repaired family is the base-scale
  triadic grid), and `FluxRowSlotsBudget.lean` was retired with it;
* the uniform ceiling `Lambda` itself is unavailable:
  `not_exists_uniform_stoppingCellLinearUpperBound_empty`
  (`FluxRowSlotsGrowthRatio.lean`) refutes the only proved source of a cell
  ceiling, `stoppingCellLinearUpperBound`, which grows linearly in `‖z_q‖`;
* along the coarse route the same budget is `K² 3^d η ≤ R^{2σ}`
  (`FluxRowSlotsCoarseSmallnessBudget`, `FluxRowSlotsCoarseBudget.lean`):
  `t`-free, cell-free and coefficient-free, hence not a property of the
  stopping rule at all.  It is met by choosing the contraction factor
  (`exists_eta_fluxRowSlots_coarse_budget_of_const`,
  `FluxRowSlotsRepairedCell.lean`), and the `t`-smallness it replaces is the
  per-cell coarse-ellipticity threshold
  `t Λ_{1/16}^{12} λ_{1/16}^{-11} ≤ (81 c³)⁻¹ η⁴` carried by
  `FluxRowSlotsCubeCoarseEllipticity`.

## What remains here

The two *geometric* facts about the repaired selection, which the coarse route
still consumes: the selection never goes below the base scale, and therefore a
radius below the base side length is below every selected side length.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- Every refined stopping cell is at least as coarse as the base scale. -/
theorem base_le_refinedStoppingScale
    (q : RefinedStoppingCell failure omega base) :
    base ≤ refinedStoppingScale q :=
  base_le_scale_of_stoppingRepairGenerated q.1.1.2



theorem le_three_pow_refinedStoppingScale_of_le_three_pow_base {R : ℝ}
    (hR : R ≤ (3 : ℝ) ^ base) (q : RefinedStoppingCell failure omega base) :
    R ≤ (3 : ℝ) ^ refinedStoppingScale q :=
  hR.trans (zpow_le_zpow_right₀ (by norm_num) (base_le_refinedStoppingScale q))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
