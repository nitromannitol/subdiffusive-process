module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffPotential
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Geometry.Cube
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
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators
noncomputable section
namespace SubdiffusiveProcess

theorem cutoffCoefficient_eq_smul_cutoffSpeedDensity
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
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
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) :
    cutoffSpeedMeasure M H omega N = weightedChaosCutoff M H N omega := by
  unfold cutoffSpeedMeasure weightedChaosCutoff
  unfold cutoffSpeedDensity fineDensity cutoffPotential finePotential
  simp only [Function.comp_def, Real.exp_add, add_sub_assoc]

/-- Paper D:18–19: the speed density is the weight times the chaos density. -/
theorem cutoffSpeedDensity_eq_exp_mul_fineDensity
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffSpeedDensity M H omega N x =
      Real.exp (H omega x) * fineDensity M N omega x := by
  unfold cutoffSpeedDensity fineDensity cutoffPotential finePotential
  rw [add_sub_assoc, Real.exp_add]

end SubdiffusiveProcess
