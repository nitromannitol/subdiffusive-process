module

public import SubdiffusiveProcess.Main.BilateralField
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

def jointPathProbabilityMeasure {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d) (x : SpatialCoordinates d) :
    ProbabilityMeasure (DiffusionPath d) := by
  letI : IsProbabilityMeasure (K (omega, x)) := hK.isProbabilityMeasure (omega, x)
  exact ⟨K (omega, x), inferInstance⟩

end SubdiffusiveProcess
