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

def physicalTimeFactor {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) : ℝ≥0 :=
  ⟨SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N,
    (div_pos
      (mul_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0) (pow_pos (by norm_num) _))
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)).le⟩

end SubdiffusiveProcess
