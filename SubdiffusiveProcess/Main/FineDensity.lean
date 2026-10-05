module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.FinePotential
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

def fineDensity {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d) : ℝ :=
  Real.exp (finePotential N omega x -
    (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)

end SubdiffusiveProcess
