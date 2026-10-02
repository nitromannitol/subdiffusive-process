import SubdiffusiveProcess.Main.PhysicalTimeFactor
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

def physicalRescaledPath {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) : DiffusionPath d → DiffusionPath d := fun path ↦
  ((3 : ℝ)⁻¹ ^ N) • path.comp
    ⟨fun t ↦ physicalTimeFactor M N * t, continuous_const.mul continuous_id⟩

end SubdiffusiveProcess
