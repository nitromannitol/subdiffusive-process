import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.IsUsualStoppingTime
import SubdiffusiveProcess.Main.MeasurableAtUsualStoppingTime
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
