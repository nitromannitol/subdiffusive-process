module

public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.BilateralField

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



abbrev in_common_scale_coupling (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
    ProbabilityMeasure (BilateralField d) :=
  commonScaleLaw d ν

end SubdiffusiveProcess.Paper
