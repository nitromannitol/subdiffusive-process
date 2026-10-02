import SubdiffusiveProcess.Paper.inputs_step_boundary
import SubdiffusiveProcess.Paper.inputs_step_interior
import SubdiffusiveProcess.Paper.inputs_step_excess
import SubdiffusiveProcess.Paper.cutoff_good_scale_input

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_step_witness (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (Paper.cutoff_good_scale_input d) := by
  exact ⟨inputs_step_boundary d hd, inputs_step_interior d hd, inputs_step_excess d hd⟩

end Paper

