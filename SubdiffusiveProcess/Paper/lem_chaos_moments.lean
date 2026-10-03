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
public import SubdiffusiveProcess.Lane3.DirichletForm
public import SubdiffusiveProcess.Lane2.KilledInverse
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Lane1.ChaosPositiveMoments
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
