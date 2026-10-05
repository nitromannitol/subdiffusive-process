module

public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

@[expose] public section

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
