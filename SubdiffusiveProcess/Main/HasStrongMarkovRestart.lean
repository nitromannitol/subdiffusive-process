module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.IsUsualStoppingTime
public import SubdiffusiveProcess.Main.MeasurableAtUsualStoppingTime
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Vocab.Ahom
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

def HasStrongMarkovRestart {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d) : Prop :=
  ∀ (x : SpatialCoordinates d) (tau : DiffusionPath d → WithTop NNReal),
    IsUsualStoppingTime (K (omega, x)) tau →
    ∀ (A : Set (DiffusionPath d)),
      MeasurableAtUsualStoppingTime (K (omega, x)) tau A →
      ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
        ∫⁻ path in A ∩ {path | tau path < ⊤},
            F (ContinuousPath.shift ((tau path).untopD 0) path) ∂(K (omega, x)) =
          ∫⁻ path in A ∩ {path | tau path < ⊤},
            ∫⁻ future, F future
              ∂(K (omega, path ((tau path).untopD 0))) ∂(K (omega, x))

end SubdiffusiveProcess
