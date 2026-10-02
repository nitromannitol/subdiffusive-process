import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Main.DiffusionPath
import SubdiffusiveProcess.Inputs.MarkovProcesses
import MarkovProcess.Trajectory.StoppingLtTop
import MarkovProcess.Path.ExitTime
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.Frozen.Vocab.Ahom
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.Metrizable.CompletelyMetrizable

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
noncomputable section
namespace SubdiffusiveProcess

def HasFiniteMeanExits {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d) : Prop :=
  ∀ U : Set (SpatialCoordinates d), IsOpen U → Bornology.IsBounded U →
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ x ∈ U,
      ∫⁻ path, ContinuousPath.exitTime U path ∂(K (omega, x)) ≤ C

end SubdiffusiveProcess
