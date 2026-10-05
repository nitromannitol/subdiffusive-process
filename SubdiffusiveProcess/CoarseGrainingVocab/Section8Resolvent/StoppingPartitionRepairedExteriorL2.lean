module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedContractionConstants
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedSourceMass

@[expose] public section

/-!
# Repaired exterior row from global and per-cell L2 contractions

This is the repaired exterior-row assembly after discharging the source mass
with the global `L2` contraction and fixing the numerical cell contraction
factor from the repaired graph constants.  The per-cell contraction is kept in
the exact shape produced by the analytic argument.

## Source

* `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open _root_.SubdiffusiveProcess.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- **The repaired exterior row with source and numerical premises
discharged.**

The global `L2` contraction supplies every source-cell bound.  The fixed
dimension-only cell factor makes the effective graph contraction exactly
`1 / 2`.  Thus the sole analytic stopping-cell input is the per-cell
contraction displayed in the statement. -/
theorem wholeSpaceSolution_exterior_decay_of_repaired_stopping_cells_of_l2
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsourceNonempty : source.Nonempty) (x0 : Vec d) (R epsilon : ℝ) (k : ℕ)
    (hgood : ¬ RepairedStoppingShortCrossing source hsourceNonempty
      x0 R epsilon k)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
        ∫ x in translatedCube d (refinedStoppingScale q)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
        repairedStoppingContractionFactor d *
          ∫ x in translatedCube d (refinedStoppingScale q + 1)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume) :
    ∫ x in (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ, u.toFun x ^ 2 ∂volume ≤
      ((stoppingGraphLevelCells repairedStoppingGraph source
          hsourceNonempty 0).card : ℝ) *
        (∫ x, f x ^ 2 ∂volume) * (1 - (1 / 2 : ℝ))⁻¹ *
        Real.exp (Real.log (1 / 2 : ℝ) * (epsilon * (3 : ℝ) ^ k)) := by
  have hbase := wholeSpaceSolution_exterior_decay_of_repaired_stopping_cells
    u hinitial hrepair source hsourceNonempty x0 R epsilon k hgood
    (A := ∫ x, f x ^ 2 ∂volume)
    (theta0 := repairedStoppingContractionFactor d)
    (integral_nonneg fun x ↦ sq_nonneg (f x))
    repairedStoppingContractionFactor_pos
    repairedStopping_effectiveContraction_lt_one
    (repairedStopping_sourceMass_le_of_l2_contraction u hL2 source
      hsourceNonempty)
    hcell
  simpa only [repairedStopping_effectiveContraction_eq_half] using hbase

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
