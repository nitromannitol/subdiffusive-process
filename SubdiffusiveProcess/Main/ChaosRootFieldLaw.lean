module

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

def chaosRootFieldLaw {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
  (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
    forget

end SubdiffusiveProcess
