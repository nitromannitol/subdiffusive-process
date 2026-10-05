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
public import SubdiffusiveProcess.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.chaos_growth_block

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/--
Non-vacuity requires inhabitation of GMCModel d at arbitrarily small disorder
and InfraredCharacterization. No zero-field witness is claimed (tauSq_pos
excludes it). This theorem has a conditional statement; a formal model witness
is a separate requirement.

 Proposition `mfd:prop-chaos-growth`, "Uniform growth and
the limiting measure", `eq:mfd-39`.  

Parameter order as the paper insists: `epsilon` is
dimensional, `p` is chosen from `epsilon` with `d < p epsilon`, and the disorder
is reduced last, so `delta0` is produced here and never assumed.

Inputs consumed: Doob's maximal inequality applied to the cube-mass
martingales; `eq:mfd-38` of `mfd:lem-chaos-moments` at order `p` and at `p = 2`;
the dyadic grid sum `Z^p = ∑_k ∑_C 2^{k p (d - epsilon)} sup_N mu_N(C)^p`, finite
by the choice of `p` and then `delta`; the portmanteau theorem on open balls for
the limit; and the tail 0-1 law of the independent layers with
`E M(Q) = |Q| > 0` for full support. -/
theorem prop_chaos_growth
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo 0 1)
    (p : ℕ) (hp : (d : ℝ) < p * epsilon) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_hH : InfraredCharacterization M H), M.delta ≤ delta0 →
      ∃ mu : BilateralField d → Measure (SpatialCoordinates d),
        Measurable mu ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally
            (fun N ↦ weightedChaosCutoff M H N omega) (mu omega) ∧
          IsLocallyFiniteMeasure (mu omega) ∧
          (mu omega).IsOpenPosMeasure ∧ NullSingletonClass (mu omega) ∧
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

end SubdiffusiveProcess.Paper
