import SubdiffusiveProcess.Main.PhysicalRescaledPath
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The rescaling map on paths is continuous

Space-time rescaling of a trajectory is composition with a fixed continuous
time change followed by a constant dilation, and both are continuous for the
compact-open topology.  Measurability is what the change of variables in the
annealed rescaling identity needs.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

theorem continuous_physicalRescaledPath
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Continuous (physicalRescaledPath M N) := by
  unfold physicalRescaledPath
  exact (continuous_const_smul _).comp
    (ContinuousMap.continuous_precomp
      (⟨fun t : ℝ≥0 => physicalTimeFactor M N * t,
        continuous_const.mul continuous_id⟩ : C(ℝ≥0, ℝ≥0)))

theorem measurable_physicalRescaledPath
    [MeasurableSpace (DiffusionPath d)] [BorelSpace (DiffusionPath d)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Measurable (physicalRescaledPath M N) :=
  (continuous_physicalRescaledPath M N).measurable

end SubdiffusiveProcess
