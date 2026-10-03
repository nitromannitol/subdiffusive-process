module

public import SubdiffusiveProcess.Paper.inputs_regularity_witness
public import SubdiffusiveProcess.Paper.lem_as_regularity

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Iteration on the caller's exact J chart and the shared produced regularity
package. No replacement chart or independently chosen Sreg occurs. -/
def inputs_iteration_witness (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : GMCModel d) (Jc : in_J d) :
    in_iteration d M Jc (inputs_regularity_witness d M) :=
  aux_lem_as_regularity_native_iteration d hd M Jc

end Paper

