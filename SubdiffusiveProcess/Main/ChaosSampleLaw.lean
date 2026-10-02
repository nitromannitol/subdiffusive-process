import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.ChaosRootFieldLaw
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Martingale.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

def chaosSampleLaw {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ProbabilityMeasure (BilateralField d) :=
  commonScaleLaw d (chaosRootFieldLaw M)

end SubdiffusiveProcess
