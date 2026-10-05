module

public import SubdiffusiveProcess.Paper.lem_band

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_hES_witness  :
    (_root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality) := by
  exact _root_.SubdiffusiveProcess.Paper.aux_lem_band_rcJ_hES

end SubdiffusiveProcess.Paper
