import SubdiffusiveProcess.Paper.inputs_deterministic_boundary
import SubdiffusiveProcess.Paper.inputs_deterministic_interior
import SubdiffusiveProcess.Paper.inputs_deterministic_excess
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_deterministic_witness (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (Paper.lane4_deterministic_good_scale_input d) := by
  exact ⟨inputs_deterministic_boundary d hd, inputs_deterministic_interior d hd, inputs_deterministic_excess d hd⟩

end Paper

