import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import SubdiffusiveProcess.Main.CutoffSpeedDensity
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.ChaosCutoff
import SubdiffusiveProcess.Main.ConditionalFineFiltration
import SubdiffusiveProcess.Main.MeasuresConvergeLocally
import SubdiffusiveProcess.Main.SemigroupSymmetric
import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
import SubdiffusiveProcess.Main.HasStrongMarkovRestart
import SubdiffusiveProcess.Main.HasFiniteMeanExits
import SubdiffusiveProcess.Main.PathLevyProkhorovDist
import SubdiffusiveProcess.Main.PhysicalRescaledPath
import SubdiffusiveProcess.Main.PhysicalTimeFactor
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.DiffusionPath
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Lane3.DirichletForm
import SubdiffusiveProcess.Lane2.KilledInverse
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Probability.CubeMassMartingale
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Inputs.MarkovProcesses
import MarkovProcess.Trajectory.StoppingLtTop
import MarkovProcess.Path.ExitTime
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.Frozen.Vocab.Ahom
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Metrizable.CompletelyMetrizable

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



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

end Paper
