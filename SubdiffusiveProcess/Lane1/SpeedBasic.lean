import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CutoffSpeedDensity
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import SubdiffusiveProcess.Main.CutoffPotential
import SubdiffusiveProcess.Main.MeasuresConvergeLocally
import SubdiffusiveProcess.Main.SemigroupSymmetric
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.ChaosCutoff
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
import SubdiffusiveProcess.Main.HasStrongMarkovRestart
import SubdiffusiveProcess.Main.HasFiniteMeanExits
import SubdiffusiveProcess.Main.PathLevyProkhorovDist
import SubdiffusiveProcess.Main.PhysicalRescaledPath
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Main.DiffusionPath
import SubdiffusiveProcess.Geometry.Cube
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
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators
noncomputable section
namespace SubdiffusiveProcess

theorem cutoffCoefficient_eq_smul_cutoffSpeedDensity
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H omega N x =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * cutoffSpeedDensity M H omega N x := by
  unfold cutoffCoefficient cutoffSpeedDensity
  aesop

theorem measuresConvergeLocally_congr
    {d : ℕ} (muN nuN : ℕ → Measure (SpatialCoordinates d))
    (mu : Measure (SpatialCoordinates d))
    (h : ∀ N, muN N = nuN N) (hc : MeasuresConvergeLocally muN mu) :
    MeasuresConvergeLocally nuN mu := by
  have hfun : muN = nuN := funext h
  rwa [hfun] at hc

theorem cutoffSpeedMeasure_eq_weightedChaosCutoff
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) :
    cutoffSpeedMeasure M H omega N = weightedChaosCutoff M H N omega := by
  unfold cutoffSpeedMeasure weightedChaosCutoff
  unfold cutoffSpeedDensity fineDensity cutoffPotential finePotential
  simp only [Function.comp_def, Real.exp_add, add_sub_assoc]

/-- Paper D:18–19: the speed density is the weight times the chaos density. -/
theorem cutoffSpeedDensity_eq_exp_mul_fineDensity
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffSpeedDensity M H omega N x =
      Real.exp (H omega x) * fineDensity M N omega x := by
  unfold cutoffSpeedDensity fineDensity cutoffPotential finePotential
  rw [add_sub_assoc, Real.exp_add]

end SubdiffusiveProcess
