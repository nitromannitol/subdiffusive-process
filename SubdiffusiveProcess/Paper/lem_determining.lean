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
import SubdiffusiveProcess.Main.IntegratedPathDetermination
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
import SubdiffusiveProcess.Paper.determining_functional_identity

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_determining
    {d : ℕ} [MeasurableSpace C(ℝ≥0, SpatialCoordinates d)]
    [BorelSpace C(ℝ≥0, SpatialCoordinates d)]
    (A : Set (BoundedContinuousFunction (SpatialCoordinates d) ℝ))
    (hcount : A.Countable)
    (hadd : ∀ f ∈ A, ∀ g ∈ A, f + g ∈ A)
    (hrat : ∀ (q : ℚ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
      f ∈ A → (q : ℝ) • f ∈ A)
    (h1 : (1 : BoundedContinuousFunction (SpatialCoordinates d) ℝ) ∈ A)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A)
    (hsep : ∀ x y : SpatialCoordinates d, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (Pm Qm : ProbabilityMeasure (DiffusionPath d))
    (heq : ∀ (k : ℕ) (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ),
      (∀ i, f i ∈ A) → ∀ m : Fin k → ℕ,
      (∫ z : DiffusionPath d,
        (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
          Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * s i)) *
            ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
        ∂(Pm : Measure (DiffusionPath d))) =
      ∫ z : DiffusionPath d,
        (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
          Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * s i)) *
            ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
        ∂(Qm : Measure (DiffusionPath d))) :
    Pm = Qm := by
  exact SubdiffusiveProcess.continuousPath_eq_of_integrated_tests A h1 hmul hsep Pm Qm heq


end Paper
