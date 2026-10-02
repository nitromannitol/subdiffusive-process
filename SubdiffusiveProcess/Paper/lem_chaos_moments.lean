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
import SubdiffusiveProcess.Lane1.ChaosPositiveMoments
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



theorem lem_chaos_moments
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (p : ℕ) (hp : 1 ≤ p) :
  ∃ Cexponent cSmall : ℝ, 0 < Cexponent ∧ 0 < cSmall ∧
    ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
      ∃ Cmass : ℝ, 0 < Cmass ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (hH : InfraredCharacterization M H), M.delta ≤ cSmall →
          (∀ (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            r ≤ 1 → (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ R →
            Measurable (fun omega ↦
              ((weightedChaosCutoff M H N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p) ∧
            Integrable (fun omega ↦
              ((weightedChaosCutoff M H N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
              (chaosSampleLaw M).toMeasure ∧
            ∫ omega, ((weightedChaosCutoff M H N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
              ∂(chaosSampleLaw M).toMeasure ≤
              Cmass * r ^ ((d : ℝ) * p - Cexponent * M.delta ^ 2)) ∧
          (∀ N omega, IsLocallyFiniteMeasure (chaosCutoff M N omega)) ∧
          (∀ N omega, IsLocallyFiniteMeasure (weightedChaosCutoff M H N omega)) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            Martingale
              (fun N omega ↦ ((chaosCutoff M N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
              (conditionalFineFiltration (fun _ ↦ 0) measurable_const)
              (chaosSampleLaw M).toMeasure ∧
            (∀ N omega, 0 ≤ ((chaosCutoff M N omega)
              (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            Martingale
              (fun N omega ↦ ((weightedChaosCutoff M H N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
              (conditionalFineFiltration H hH.1) (chaosSampleLaw M).toMeasure ∧
            (∀ N omega, 0 ≤ ((weightedChaosCutoff M H N omega)
              (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)) :=
  SubdiffusiveProcess.chaos_positive_moments_and_martingales hd p hp

end Paper
