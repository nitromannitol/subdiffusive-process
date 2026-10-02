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

def SemigroupSymmetric {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (mu : Measure (SpatialCoordinates d)) : Prop :=
  ∀ (t : ℝ≥0) (f g : SpatialCoordinates d → ℝ≥0∞),
    Measurable f → Measurable g →
    ∫⁻ x, f x * (∫⁻ y, g y ∂P t x) ∂mu =
      ∫⁻ x, g x * (∫⁻ y, f y ∂P t x) ∂mu

end SubdiffusiveProcess
