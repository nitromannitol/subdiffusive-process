module

public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.ExcessDecay.LiveAssembly
public import SubdiffusiveProcess.Analysis.SmoothDualBoundaryClauseSix
public import SubdiffusiveProcess.Analysis.SmoothDualInteriorGeneric

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SubdiffusiveProcess.Paper

/-- **Lemma `l.cutoff.regularity.good.scale.estimates`**,
proved: the published arbitrary-cutoff one-scale input `cutoff_good_scale_input` holds, at the
manuscript powers `s^{-3/2}, s^{-15/2}, s^{-7/2}` (harmonic approximation) and
`s^{-3/2}, s^{-15/2}, s^{-3}` (excess decay).

* Clause 1 (harmonic approximation, boundary regime) is
  `SubdiffusiveProcess.Analysis.aux_b12bd_boundaryClause_six`.
* Clause 2 (interior harmonic approximation) is
  `interiorCutoffHarmonicApproximationInput_smoothDual_viaReads`.
* Clause 3 (excess decay, both the containment and the boundary-touching branch) is
  `SubdiffusiveProcess.ExcessDecayLive.cutoffExcessDecay_live` — the deterministic excess-decay
  iteration replayed at the live powers from clause 1. -/
theorem cutoff_good_scale_estimates (d : ℕ) [NeZero d] : cutoff_good_scale_input d :=
  ⟨SubdiffusiveProcess.Analysis.aux_b12bd_boundaryClause_six d,
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.SmoothDualComparison.interiorCutoffHarmonicApproximationInput_smoothDual_viaReads
      d,
    SubdiffusiveProcess.ExcessDecayLive.cutoffExcessDecay_live d
      (SubdiffusiveProcess.Analysis.aux_b12bd_boundaryClause_six d)⟩

end SubdiffusiveProcess.Paper
