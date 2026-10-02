import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.ExcessDecay.LiveAssembly
import SubdiffusiveProcess.Analysis.SmoothDualBoundaryClauseSix
import SubdiffusiveProcess.Analysis.SmoothDualInteriorGeneric

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
