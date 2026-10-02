import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Main.BilateralField

open MeasureTheory
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



abbrev in_common_scale_coupling (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
    ProbabilityMeasure (BilateralField d) :=
  commonScaleLaw d ν

end Paper
