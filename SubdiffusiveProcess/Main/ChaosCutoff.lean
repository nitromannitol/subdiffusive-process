module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.FineDensity
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

def chaosCutoff {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N : ℕ) (omega : BilateralField d) : Measure (SpatialCoordinates d) :=
  volume.withDensity (ENNReal.ofReal ∘ fineDensity M N omega)

end SubdiffusiveProcess
