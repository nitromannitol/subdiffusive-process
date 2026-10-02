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

def chaosRootFieldLaw {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
  (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
    forget.continuous.measurable.aemeasurable

end SubdiffusiveProcess
