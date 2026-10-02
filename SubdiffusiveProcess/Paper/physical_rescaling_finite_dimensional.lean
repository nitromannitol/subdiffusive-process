import SubdiffusiveProcess.Paper.physical_generator_reindexing
import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
import SubdiffusiveProcess.Main.PhysicalRescaledPath
import SubdiffusiveProcess.Lane1.RescaledPath
import SubdiffusiveProcess.Main.DiffusionPath
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
open scoped CompactlySupported ENNReal NNReal LevyProkhorov

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem physical_rescaling_finite_dimensional
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (sigma : ℕ → BilateralField d → BilateralField d)
    (hsigmadef : ∀ N omega (j : ℤ) (x : SpatialCoordinates d),
      sigma N omega j x = omega (j + (N : ℤ)) (((3 : ℝ) ^ N) • x))
    (htransport : ∀ N omega (x : SpatialCoordinates d),
      Measure.map (physicalRescaledPath M N)
        (KN 0 (omega, (3 : ℝ) ^ N • x)) =
          KN N (sigma N omega, x)) :
    ∀ (N : ℕ), ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x : SpatialCoordinates d, ∀ I : Finset NNReal,
        (Measure.map (physicalRescaledPath M N)
            (KN 0 (omega, (3 : ℝ) ^ N • x))).map
              (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN N (sigma N omega)) I x := by
  obtain ⟨hmp, _⟩ := physical_generator_reindexing hd M H hH PN KN hKN hin sigma hsigmadef htransport
  intro N
  have hpush := (hmp N).quasiMeasurePreserving.ae hin.2.2
  filter_upwards [hpush] with omega hP
  intro x I
  rw [htransport N omega x, ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
  exact hP N I x


end Paper
