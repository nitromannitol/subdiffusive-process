import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.FineDensity
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

def chaosCutoff {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) : Measure (SpatialCoordinates d) :=
  volume.withDensity (ENNReal.ofReal ∘ fineDensity M N omega)

end SubdiffusiveProcess
