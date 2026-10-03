module

public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.ExcessDecay.LiveAssembly
public import SubdiffusiveProcess.Analysis.SmoothDualBoundaryClauseSix
public import SubdiffusiveProcess.Analysis.SmoothDualInteriorGeneric

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Paper



theorem cutoff_good_scale_estimates (d : ℕ) [NeZero d] : cutoff_good_scale_input d :=
  ⟨SubdiffusiveProcess.Analysis.aux_b12bd_boundaryClause_six d,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.SmoothDualScratch.interiorCutoffHarmonicApproximationInput_smoothDual_viaReads
      d,
    SubdiffusiveProcess.ExcessDecayLive.cutoffExcessDecay_live d
      (SubdiffusiveProcess.Analysis.aux_b12bd_boundaryClause_six d)⟩

end Paper
