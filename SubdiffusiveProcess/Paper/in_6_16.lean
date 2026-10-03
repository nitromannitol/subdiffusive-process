module

public import SubdiffusiveProcess.Lane4.Inputs

@[expose] public section

open MeasureTheory Set TopologicalSpace Filter Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



abbrev in_6_16 (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) : Type :=
  PaperSourcedRegularity d M

end Paper
