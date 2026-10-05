
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffCellEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffSharpLoop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicEllipticityCaps

@[expose] public section

/-!
# The finite-cutoff leaves of the boundary harmonic chain, under their uncut names

The boundary harmonic chain consumes the good event at a short list of leaves.
Every one of them already exists in cutoff form, either in
`Section6HolderBelowCutoff` (interior cutoff re-run) or in
`Section6CutoffHarmonic` itself.  This module re-exports each cutoff leaf under
*the name its uncut original carries*, inside the namespace
`SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic`.

That namespace is opened last in every downstream cutoff module, so a reference
to, say, `exists_localBoundaryEllipticityCaps_nextWindow` resolves to the cutoff
leaf while every untouched deterministic lemma still resolves to the committed
uncut one.  This is what lets the boundary chain be re-run at `𝒢^{(L)}` by a
pure binder edit, with no proof-script surgery at the leaves.

Each alias is a definitional re-export: the aliased statement is the uncut one
with the binder `m ≤ L` (resp. `n + 2 ≤ L`, `k ≤ L`) deleted and
`goodEvent M none` replaced by `goodEvent M (some L)`.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

/-- Cutoff form of `Section6HarmonicApproximation.exists_section6HomogenizationError_le_of_goodEvent`. -/
alias exists_section6HomogenizationError_le_of_goodEvent :=
  Section6HolderBelowCutoff.exists_section6HomogenizationError_le_of_cutoffGoodEvent

/-- Cutoff form of
`Section6HarmonicApproximation.homogenizationErrorOnCube_aCutoff_le_section6_of_goodEvent`. -/
alias homogenizationErrorOnCube_aCutoff_le_section6_of_goodEvent :=
  Section6HolderBelowCutoff.homogenizationErrorOnCube_aCutoff_le_section6_of_cutoffGoodEvent

/-- Cutoff form of
`Section6HarmonicApproximation.localHomogenizationError_two_le_anchor_of_closedContainment`. -/
alias localHomogenizationError_two_le_anchor_of_closedContainment :=
  Section6HolderBelowCutoff.localHomogenizationError_two_le_cutoffAnchor_of_closedContainment

/-- Cutoff form of
`Section6HarmonicApproximation.localHomogenizationError_two_le_anchor_nextWindow`. -/
alias localHomogenizationError_two_le_anchor_nextWindow :=
  Section6HolderBelowCutoff.localHomogenizationError_two_le_cutoffAnchor_nextWindow

/-- Cutoff form of
`Section6HarmonicApproximation.exists_localBoundaryEllipticityCaps_nextWindow`. -/
alias exists_localBoundaryEllipticityCaps_nextWindow :=
  Section6HolderBelowCutoff.exists_localCutoffEllipticityCaps_nextWindow

/-- Cutoff form of
`Section6HarmonicApproximation.exists_interiorCellEnergy_le_manuscriptPrices`. -/
alias exists_interiorCellEnergy_le_manuscriptPrices :=
  Section6HolderBelowCutoff.exists_interiorCellEnergy_le_manuscriptPrices_datumCutoff

/-- Cutoff form of
`Section6HarmonicApproximation.exists_cubeLpNorm_sub_le_flatComparatorGoodEventBound_sharp`. -/
alias exists_cubeLpNorm_sub_le_flatComparatorGoodEventBound_sharp :=
  Section6HolderBelowCutoff.exists_cubeLpNorm_sub_le_flatComparatorCutoffGoodEventBound_sharp

/-- Cutoff form of
`Section6HarmonicApproximation.exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorGoodEvent_sharp`. -/
alias exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorGoodEvent_sharp :=
  Section6HolderBelowCutoff.exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorCutoffGoodEvent_sharp

/-- Cutoff form of
`Section6HarmonicApproximation.exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp`. -/
alias exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp :=
  Section6HolderBelowCutoff.exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_sharp

/-- Cutoff form of
`Section6HarmonicInterior.exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp_neZero`. -/
alias exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp_neZero :=
  Section6HolderBelowCutoff.exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_sharp_neZero

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
