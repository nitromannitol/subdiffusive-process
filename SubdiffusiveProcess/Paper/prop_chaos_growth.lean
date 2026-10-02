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
import SubdiffusiveProcess.Paper.chaos_growth_block

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem prop_chaos_growth
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo 0 1)
    (p : ℕ) (hp : (d : ℝ) < p * epsilon) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (hH : InfraredCharacterization M H), M.delta ≤ delta0 →
      ∃ mu : BilateralField d → Measure (SpatialCoordinates d),
        Measurable mu ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally
            (fun N ↦ weightedChaosCutoff M H N omega) (mu omega) ∧
          IsLocallyFiniteMeasure (mu omega) ∧
          (mu omega).IsOpenPosMeasure ∧ NoAtoms (mu omega) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            mu omega (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)) ∧
        ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Kmu : BilateralField d → ℝ,
            MemLp Kmu p (chaosSampleLaw M).toMeasure ∧
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              0 ≤ Kmu omega ∧
              (∀ N x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                weightedChaosCutoff M H N omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon))) ∧
              (∀ x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                mu omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon))) := by
  obtain ⟨delta0, hdelta0, hmain⟩ := chaos_growth_block hd epsilon hepsilon p hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M H hH hdM
  obtain ⟨mu, hmeas, hconv, hreg, hK⟩ := hmain M H hH hdM
  refine ⟨mu, hmeas, ?_, hK⟩
  filter_upwards [hconv, hreg] with omega h1 h2
  exact ⟨h1, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

end Paper
