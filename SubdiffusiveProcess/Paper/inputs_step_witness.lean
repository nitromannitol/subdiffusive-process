module

public import SubdiffusiveProcess.Paper.inputs_step_boundary
public import SubdiffusiveProcess.Paper.inputs_step_interior
public import SubdiffusiveProcess.Paper.inputs_step_excess
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_step_witness (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (_root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d) := by
  exact ⟨inputs_step_boundary d hd, inputs_step_interior d hd, inputs_step_excess d hd⟩

end SubdiffusiveProcess.Paper
