module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.ChaosRootFieldLaw
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

def chaosSampleLaw {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ProbabilityMeasure (BilateralField d) :=
  commonScaleLaw d (chaosRootFieldLaw M)

end SubdiffusiveProcess
