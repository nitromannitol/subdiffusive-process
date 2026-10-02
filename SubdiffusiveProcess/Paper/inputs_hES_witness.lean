import SubdiffusiveProcess.Paper.lem_band

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_hES_witness  :
    (SubdiffusiveProcess.Lane3.EfronSteinMomentInequality) := by
  exact Paper.aux_lem_band_rcJ_hES

end Paper

