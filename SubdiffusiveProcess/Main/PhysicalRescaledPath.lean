module

public import SubdiffusiveProcess.Main.PhysicalTimeFactor
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

/-!
# Space and time rescaling of a physical path

`physicalRescaledPath M N` sends `path(t)` to
`3^(-N) path(physicalTimeFactor M N * t)`. Both paths are continuous maps
from nonnegative time to spatial coordinates. Theorem A integrates the
level-zero cutoff kernel started at `3^N x`, then applies this map to obtain
the annealed law at physical starting point `x`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
noncomputable section
namespace SubdiffusiveProcess

def physicalRescaledPath {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N : ℕ) : DiffusionPath d → DiffusionPath d := fun path ↦
  ((3 : ℝ)⁻¹ ^ N) • path.comp
    ⟨fun t ↦ physicalTimeFactor M N * t, continuous_const.mul continuous_id⟩

end SubdiffusiveProcess
