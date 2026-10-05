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
public import SubdiffusiveProcess.Main.IntegratedPathDetermination
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
public import SubdiffusiveProcess.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.determining_functional_identity

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem lem_determining
    {d : ℕ} [MeasurableSpace C(ℝ≥0, SpatialCoordinates d)]
    [BorelSpace C(ℝ≥0, SpatialCoordinates d)]
    (A : Set (BoundedContinuousFunction (SpatialCoordinates d) ℝ))
    (_hcount : A.Countable)
    (_hadd : ∀ f ∈ A, ∀ g ∈ A, f + g ∈ A)
    (_hrat : ∀ (q : ℚ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
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


end SubdiffusiveProcess.Paper
