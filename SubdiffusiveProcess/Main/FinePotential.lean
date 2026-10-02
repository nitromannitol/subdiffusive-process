import SubdiffusiveProcess.Main.BilateralField
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

def finePotential {d : ℕ} (N : ℕ) (omega : BilateralField d)
    (x : SpatialCoordinates d) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)) x

end SubdiffusiveProcess
