module

public import SubdiffusiveProcess.Paper.prop_growth_macro_energy

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The original-field regularity package, retaining its pinned dimensional
constant, common prefix and all-environment guarded estimates. -/
def inputs_regularity_witness (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : GMCModel d) : in_6_16 d M :=
  aux_prop_growth_macro_energy_nativeSreg M

end SubdiffusiveProcess.Paper

