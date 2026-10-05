module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.AnchorShapes
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.Multiplier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.PackageAssembly

@[expose] public section

/-!
# The completed passages in the Section 6 Holder lift

This file records the exact conditional excess input and the already completed
Campanato and good-scale bookkeeping passages.  It also exposes the precise
factorization of the two anchor shapes through the remaining energy and
finite-cutoff rows.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

/-- The boundary-row input is definitionally the exact conclusion block of
the excess-decay anchor. -/
theorem boundaryHolderExcessDecayInput_of_statedShape {d : ℕ}
    (hExcess : Section6Holder.HolderExcessDecayInput d) :
    BoundaryHolderExcessDecayInput d := by
  exact hExcess

/-- The Campanato-to-Holder passage: excess decay, stopped-scale iteration,
off-grid rebasing, and the shallow/top-scale cases produce the first
row.  The full inferred type is kept so that no weakened facade is introduced. -/
theorem campanatoToHolderPassage {d : ℕ} [NeZero d]
    (hExcess : Section6Holder.HolderExcessDecayInput d) :
    type_of% (exists_boundaryRowOneAtStepFree d hExcess) :=
  exists_boundaryRowOneAtStepFree d hExcess

/-- The good-scale bookkeeping passage used by the final short-scale excess
readout produces the third row. -/
theorem goodScaleBookkeepingPassage {d : ℕ} [NeZero d]
    (hExcess : Section6Holder.HolderExcessDecayInput d) :
    type_of% (exists_boundaryRowThreeAtStepFree d
    (boundaryHolderExcessDecayInput_of_statedShape hExcess)) :=
  exists_boundaryRowThreeAtStepFree d
    (boundaryHolderExcessDecayInput_of_statedShape hExcess)

/-- In dimension zero both exact anchor shapes are automatic, because the GMC
model carries the contradictory dimensional requirement `2 ≤ 0`. -/
theorem holderRegularityInput_zero : HolderRegularityInput 0 := by
  refine ⟨1, by norm_num, ?_⟩
  intro M
  have hdim : 2 ≤ 0 := M.shellPrefix.dimension
  omega

/-- Dimension-zero cutoff companion. -/
theorem cutoffHolderRegularityInput_zero : CutoffHolderRegularityInput 0 := by
  refine ⟨1, by norm_num, ?_⟩
  intro M
  have hdim : 2 ≤ 0 := M.shellPrefix.dimension
  omega

/-- The cutoff-independent anchor is the common-carrier conjunct of the
cutoff companion, instantiated at `L = m`.  This carrier specialization
introduces no analytic hypothesis. -/
theorem holderRegularityInput_of_cutoffHolderRegularityInput {d : ℕ}
    (hcutoff : CutoffHolderRegularityInput d) :
    HolderRegularityInput d := by
  obtain ⟨C, hC, hall⟩ := hcutoff
  refine ⟨C, hC, ?_⟩
  intro M hdelta alpha halpha m
  exact (hall M hdelta alpha halpha m m).2.1 le_rfl
end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
