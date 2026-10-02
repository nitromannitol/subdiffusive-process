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
import SubdiffusiveProcess.Paper.lem_chaos_moments
import SubdiffusiveProcess.Paper.chaos_growth_cutoff
import SubdiffusiveProcess.Paper.chaos_test_martingale
import SubdiffusiveProcess.Paper.chaos_vague_limit
import SubdiffusiveProcess.Paper.chaos_limit_growth
import SubdiffusiveProcess.Paper.chaos_limit_locfin_noatoms
import SubdiffusiveProcess.Paper.chaos_limit_null_frontier
import SubdiffusiveProcess.Paper.chaos_mean_positive
import SubdiffusiveProcess.Paper.chaos_tail_law
import SubdiffusiveProcess.Paper.chaos_full_support

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem chaos_growth_block
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo 0 1)
    (p : ℕ) (hp : (d : ℝ) < p * epsilon) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∃ mu : BilateralField d → Measure (SpatialCoordinates d),
          Measurable mu ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            MeasuresConvergeLocally
              (fun N ↦ weightedChaosCutoff M H N omega) (mu omega)) ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            IsLocallyFiniteMeasure (mu omega) ∧
            (mu omega).IsOpenPosMeasure ∧ NoAtoms (mu omega) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
              mu omega
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)) ∧
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
  classical
  obtain ⟨hep0, hep1⟩ := hepsilon
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp2 : 2 ≤ p := by
    have hpR : (2 : ℝ) < (p : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) p]
    exact_mod_cast hpR.le
  obtain ⟨delta1, hdelta1pos, hgrowthAll⟩ :=
    Paper.chaos_growth_cutoff hd epsilon ⟨hep0, hep1⟩ p hp
  obtain ⟨Cexp, cSmall, hCexp, hcSmallpos, hmomAll⟩ :=
    Paper.lem_chaos_moments hd p (le_trans one_le_two hp2)
  refine ⟨min delta1 cSmall, lt_min hdelta1pos hcSmallpos, ?_⟩
  intro M H hH hdelta
  have hdelta1 : M.delta ≤ delta1 := le_trans hdelta (min_le_left _ _)
  have hdeltac : M.delta ≤ cSmall := le_trans hdelta (min_le_right _ _)
  have hmart : ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) →
      Martingale (fun N omega => ∫ x, f x ∂(weightedChaosCutoff M H N omega))
        (conditionalFineFiltration H hH.1) (chaosSampleLaw M).toMeasure :=
    fun f hf => (Paper.chaos_test_martingale hd M H hH f hf).1
  obtain ⟨mu, hmumble, hlocfin, hinner, hvague⟩ :=
    Paper.chaos_vague_limit hd epsilon ⟨hep0, hep1⟩ p hp M H hH hmart
      (hgrowthAll M H hH hdelta1)
  -- the growth bound passes to the limit
  have hlimgrowth : ∀ R : Set (SpatialCoordinates d), Bornology.IsBounded R →
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
    intro R hR
    obtain ⟨Kmu, hKLp, hKae⟩ := hgrowthAll M H hH hdelta1 R hR
    refine ⟨Kmu, hKLp, ?_⟩
    filter_upwards [hKae, hvague] with omega hom homega
    exact ⟨hom.1, hom.2, Paper.chaos_limit_growth epsilon (Kmu omega) hom.1
      (mu omega) (fun N => weightedChaosCutoff M H N omega) homega
      (hinner omega) R hom.2⟩
  -- the limit's growth bound holds for all bounded sets at once, almost surely
  have hballgrowth : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ n : ℕ,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (n : ℝ),
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          mu omega (Metric.ball x r) ≤
            ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon)) := by
    rw [ae_all_iff]
    intro n
    obtain ⟨Kmu, hKLp, hKae⟩ :=
      hlimgrowth (Metric.ball (0 : SpatialCoordinates d) (n : ℝ))
        Metric.isBounded_ball
    filter_upwards [hKae] with omega hom
    exact ⟨Kmu omega, hom.1, fun x hx r hr hr1 => hom.2.2 x hx r hr hr1⟩
  have hgrowthae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ Rset : Set (SpatialCoordinates d), Bornology.IsBounded Rset →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Rset, ∀ r : ℝ, 0 < r → r ≤ 1 →
          mu omega (Metric.ball x r) ≤
            ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon)) := by
    filter_upwards [hballgrowth] with omega hom
    intro Rset hRset
    obtain ⟨rr, hrr⟩ := hRset.subset_ball (0 : SpatialCoordinates d)
    obtain ⟨n, hnn⟩ := exists_nat_gt rr
    obtain ⟨K, hK0, hKb⟩ := hom n
    exact ⟨K, hK0, fun x hx => hKb x (hrr.trans (Metric.ball_subset_ball hnn.le) hx)⟩
  -- positivity of the mean, cube by cube
  have hmean : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      0 < ∫⁻ omega, mu omega (centeredCube z r hr : Set (SpatialCoordinates d))
        ∂(chaosSampleLaw M).toMeasure := by
    have hsmall : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
        0 < ∫⁻ omega, mu omega (centeredCube z r hr : Set (SpatialCoordinates d))
          ∂(chaosSampleLaw M).toMeasure := by
      intro z r hr hr1
      obtain ⟨Cmass, hCmass, hmomR⟩ :=
        hmomAll (centeredCube z r hr : Set (SpatialCoordinates d)) (by
          rw [centeredCube_coe_eq_ball]; exact Metric.isBounded_ball)
      have hstep := (hmomR M H hH hdeltac).1
      refine Paper.chaos_mean_positive hd M H hH mu hmumble hlocfin z r hr p hp2
        (Cmass * r ^ ((d : ℝ) * p - Cexp * M.delta ^ 2)) ?_ ?_ hvague
      · exact fun N => (hstep N z r hr hr1 (subset_refl _)).2.1
      · exact fun N => (hstep N z r hr hr1 (subset_refl _)).2.2
    intro z r hr
    rcases le_or_lt r 1 with hr1 | hr1
    · exact hsmall z r hr hr1
    · refine lt_of_lt_of_le (hsmall z 1 one_pos le_rfl) ?_
      refine lintegral_mono fun omega => measure_mono ?_
      rw [centeredCube_coe_eq_ball, centeredCube_coe_eq_ball]
      exact Metric.ball_subset_ball (by linarith)
  have hfullsupp : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (mu omega).IsOpenPosMeasure :=
    Paper.chaos_full_support hd M mu hmumble hmean
      (Paper.chaos_tail_law hd M H mu hmumble hlocfin hvague)
  refine ⟨mu, hmumble, hvague, ?_, hlimgrowth⟩
  filter_upwards [hgrowthae, hfullsupp] with omega hg hf
  exact ⟨hlocfin omega, hf,
    (Paper.chaos_limit_locfin_noatoms hd epsilon ⟨hep0, hep1⟩ (mu omega) hg).2,
    Paper.chaos_limit_null_frontier hd epsilon ⟨hep0, hep1⟩ (mu omega) hg⟩

end Paper
