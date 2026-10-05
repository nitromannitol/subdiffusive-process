module

public import SubdiffusiveProcess.Paper.inputs_deterministic_boundary
public import SubdiffusiveProcess.Paper.inputs_deterministic_interior
public import SubdiffusiveProcess.Paper.inputs_deterministic_excess
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_deterministic_witness (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (_root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) := by
  exact ⟨inputs_deterministic_boundary d hd, inputs_deterministic_interior d hd, inputs_deterministic_excess d hd⟩

end SubdiffusiveProcess.Paper

