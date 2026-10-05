module

public import SubdiffusiveProcess.Paper.physical_generator_reindexing
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.MultiplicativeChaos.RescaledPath
public import SubdiffusiveProcess.Main.DiffusionPath
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
open scoped CompactlySupported ENNReal NNReal LevyProkhorov

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Fine proof step for the physical-rescaling identity.  This is the finite-dimensional comparison used before the path
measure determination argument in `physical_rescaling`.

Inputs:
- `physical_generator_reindexing` supplies the reindexed generator and
  clock computation used to identify the transformed process;
- `in_crossing` supplies the cutoff semigroup's weak-resolvent and
  finite-dimensional attachment;
- `hH`, `hKN`, and the displayed reindexing equation are the standing
  model, path-kernel, and environment-map data of the parent;
- `htransport` carries the physical-law identification used by the
  reindexing theorem: the rescaled cutoff-zero path law is the cutoff-`N`
  path law in the reindexed environment.  Its supplier is the physical
  diffusion identification, recorded by
  `physical_generator_reindexing` and;
- the conclusion is only the finite-dimensional comparison; path-measure
  equality and the annealed change of variables remain in the parent;
- no arbitrary coefficient-pair uniqueness premise is introduced.
-/
theorem physical_rescaling_finite_dimensional
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
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


end SubdiffusiveProcess.Paper
