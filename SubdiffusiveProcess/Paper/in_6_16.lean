module

public import SubdiffusiveProcess.EllipticRegularity.Inputs

@[expose] public section

open MeasureTheory Set TopologicalSpace Filter Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



abbrev in_6_16 (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : Type :=
  PaperSourcedRegularity d M

end SubdiffusiveProcess.Paper
