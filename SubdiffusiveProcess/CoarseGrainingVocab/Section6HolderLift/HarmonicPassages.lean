module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodScaleAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.Passages

@[expose] public section

/-!
# Holder passages from the harmonic good-scale carrier

The good-scale excess conclusion is no longer an independent input to the
Holder lift: the Section 6 excess-decay assembly derives its exact v4 carrier
from the Prop-valued v6 harmonic conclusion.  This file installs that result
in both Holder excess interfaces and removes the redundant excess premise from
the two exact anchor factorizations.

Argument: `ss.good.scale.estimates` and `ss.regularity.iteration`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

/-- The exact Holder excess carrier follows from the exact harmonic carrier.
The dimension-zero case is handled inside the excess-decay assembly. -/
theorem holderExcessDecayInput_of_harmonicInput (d : ℕ)
    (hHarmonic : Section6ExcessDecay.HarmonicApproximationInput d) :
    Section6Holder.HolderExcessDecayInput d := by
  simpa only [Section6Holder.HolderExcessDecayInput] using
    Section6ExcessDecay.excess_decay_good_scales_of_harmonic_approximation_good_scales
      d (fun _ ↦ hHarmonic)

/-- The boundary Holder iteration uses a second name for the same byte-exact
v4 excess conclusion. -/
theorem boundaryHolderExcessDecayInput_of_harmonicInput (d : ℕ)
    (hHarmonic : Section6ExcessDecay.HarmonicApproximationInput d) :
    BoundaryHolderExcessDecayInput d := by
  exact boundaryHolderExcessDecayInput_of_frozenShape
    (holderExcessDecayInput_of_harmonicInput d hHarmonic)



theorem campanatoToHolderPassage_of_harmonicInput
    {d : ℕ} [NeZero d]
    (hHarmonic : Section6ExcessDecay.HarmonicApproximationInput d) :
    type_of% (campanatoToHolderPassage
    (holderExcessDecayInput_of_harmonicInput d hHarmonic)) :=
  campanatoToHolderPassage
    (holderExcessDecayInput_of_harmonicInput d hHarmonic)



theorem goodScaleBookkeepingPassage_of_harmonicInput
    {d : ℕ} [NeZero d]
    (hHarmonic : Section6ExcessDecay.HarmonicApproximationInput d) :
    type_of% (goodScaleBookkeepingPassage
    (holderExcessDecayInput_of_harmonicInput d hHarmonic)) :=
  goodScaleBookkeepingPassage
    (holderExcessDecayInput_of_harmonicInput d hHarmonic)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
