module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Paper.inputs_Interp_interpolation
public import SubdiffusiveProcess.Paper.inputs_Interp_compact

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_Interp_witness (d : ℕ) (hd : 2 ≤ d) :
    CubeFractionalInterpolationInput d hd := by
  exact ⟨inputs_Interp_interpolation d hd, inputs_Interp_compact d hd⟩

end SubdiffusiveProcess.Paper
