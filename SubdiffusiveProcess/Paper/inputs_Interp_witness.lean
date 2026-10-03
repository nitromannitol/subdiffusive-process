module

public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Paper.inputs_Interp_interpolation
public import SubdiffusiveProcess.Paper.inputs_Interp_compact

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem inputs_Interp_witness (d : ℕ) (hd : 2 ≤ d) :
    CubeFractionalInterpolationInput d hd := by
  exact ⟨inputs_Interp_interpolation d hd, inputs_Interp_compact d hd⟩

end Paper
