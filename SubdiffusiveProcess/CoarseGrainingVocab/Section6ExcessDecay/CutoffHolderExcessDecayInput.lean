module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffExcessAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.CutoffHarmonicBoundaryInput

@[expose] public section

/-!
# The boundary excess-decay input at a finite cutoff

`BoundaryCutoffHolderExcessDecayInputV4` is the v4 excess-decay conclusion of
`l.excess.decay.good.scales.GMC` with the two source-prescribed changes of
paper label `l.excess.decay.good.scales.GMC`: the premise `m ≤ L` is deleted and the
good event is `goodEvent M (some L)`.

`BelowCutoffExcessAssembly.belowCutoffHolderExcessDecay_of_harmonic` already
derives it from the matching cutoff harmonic package and the cutoff `𝓔` cap,
by the route `AnchorBoundary.lean` takes in the uncut case.  Since the
harmonic package is a theorem, so the excess-decay input is unconditional.

paper label `l.excess.decay.good.scales.GMC` re-run on `𝒢^{(L)}`, i.e.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The boundary excess-decay input on the finite-cutoff good event.**  This
is the v4 excess-decay conclusion with `m ≤ L` deleted and the good
event replaced by `𝒢^{(L)}`. -/
theorem boundaryCutoffHolderExcessDecayInputV4 (d : ℕ) [NeZero d] :
    BoundaryCutoffHolderExcessDecayInputV4 d :=
  belowCutoffHolderExcessDecay_of_harmonic d
    (boundaryCutoffHarmonicApproximationInputV6 d)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
