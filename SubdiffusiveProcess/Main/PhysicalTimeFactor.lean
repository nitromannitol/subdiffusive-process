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

def physicalTimeFactor {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) : ℝ≥0 :=
  ⟨SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N,
    (div_pos
      (mul_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0) (pow_pos (by norm_num) _))
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)).le⟩

end SubdiffusiveProcess
