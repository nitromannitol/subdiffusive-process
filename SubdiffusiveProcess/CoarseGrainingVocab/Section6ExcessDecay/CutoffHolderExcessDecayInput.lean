module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffExcessAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.CutoffHarmonicBoundaryInput

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The boundary excess-decay input on the finite-cutoff good event.**  This
is the frozen v4 excess-decay conclusion with `m ≤ L` deleted and the good
event replaced by `𝒢^{(L)}`. -/
theorem boundaryCutoffHolderExcessDecayInputV4 (d : ℕ) [NeZero d] :
    BoundaryCutoffHolderExcessDecayInputV4 d :=
  belowCutoffHolderExcessDecay_of_harmonic d
    (boundaryCutoffHarmonicApproximationInputV6 d)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
