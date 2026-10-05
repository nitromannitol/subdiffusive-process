module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Main.PhysicalTimeFactor
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.VariationalResponses.KilledInverse
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem cube_exhaustion (d : ℕ) :
    ∃ (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n),
      (∀ n : ℕ, ∃ k : ℤ, Qr n = (3 : ℝ) ^ k) ∧
      ∀ U : Set (SpatialCoordinates d), Bornology.IsBounded U →
        ∃ n : ℕ, U ⊆ (centeredCube (Qc n) (Qr n) (hQr n) :
          Set (SpatialCoordinates d)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (3 : ℝ) ^ n := fun n => by positivity
  refine ⟨fun _ => 0, fun n => (3 : ℝ) ^ n, hpos, ?_, ?_⟩
  · intro n
    exact ⟨(n : ℤ), by rw [zpow_natCast]⟩
  intro U hU
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : SpatialCoordinates d)).1 hU
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max R 0 * 2 + 1) (by norm_num : (1:ℝ) < 3)
  refine ⟨n, ?_⟩
  show U ⊆ Metric.ball (0 : SpatialCoordinates d) ((3 : ℝ) ^ n / 2)
  refine hR.trans (Metric.closedBall_subset_ball ?_)
  have h0 : R ≤ max R 0 := le_max_left _ _
  have h1 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  linarith

end SubdiffusiveProcess.Paper
