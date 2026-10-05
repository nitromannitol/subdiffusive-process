module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Probability.Martingale.Basic
public import SubdiffusiveProcess.MultiplicativeChaos.GrowthCutoff
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import SubdiffusiveProcess.MultiplicativeChaos.VagueLimit

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem chaos_vague_limit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (_hepsilon : epsilon ∈ Set.Ioo 0 1)
    (p : ℕ) (_hp : (d : ℝ) < p * epsilon)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (_hmart : ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) →
      Martingale (fun N omega => ∫ x, f x ∂(weightedChaosCutoff M H N omega))
        (conditionalFineFiltration H hH.1) (chaosSampleLaw M).toMeasure)
    (_hgrowth : ∀ Rset : Set (SpatialCoordinates d), Bornology.IsBounded Rset →
      ∃ Kmu : BilateralField d → ℝ,
        MemLp Kmu p (chaosSampleLaw M).toMeasure ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          0 ≤ Kmu omega ∧
          ∀ N x, x ∈ Rset → ∀ r, 0 < r → r ≤ 1 →
            weightedChaosCutoff M H N omega (Metric.ball x r) ≤
              ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon))) :
    ∃ mu : BilateralField d → Measure (SpatialCoordinates d),
      Measurable mu ∧
      (∀ omega, IsLocallyFiniteMeasure (mu omega)) ∧
      (∀ (omega : BilateralField d) (U : Set (SpatialCoordinates d)), IsOpen U →
        ∀ c : ℝ≥0∞, c < mu omega U →
          ∃ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
            tsupport (f : SpatialCoordinates d → ℝ) ⊆ U ∧
            c < ENNReal.ofReal (∫ x, f x ∂(mu omega))) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        MeasuresConvergeLocally
          (fun N ↦ weightedChaosCutoff M H N omega) (mu omega) := by
  refine SubdiffusiveProcess.chaos_vague_limit_of_cube_limits M H hH ?_
  have h1 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (j : ℕ) (k : Fin d → ℤ), ∃ L : ℝ, Filter.Tendsto (fun N =>
        ((weightedChaosCutoff M H N omega)
          ((centeredCube (SubdiffusiveProcess.tileCenter j k)
            ((3 : ℝ) ^ (-(j : ℤ))) (SubdiffusiveProcess.zpow_neg_pos j)) :
              Set (SpatialCoordinates d))).toReal) Filter.atTop (nhds L) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    exact SubdiffusiveProcess.chaos_cube_ae_tendsto hd M H hH _ _ _
  have h2 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ n : ℕ, ∃ L : ℝ, Filter.Tendsto (fun N =>
        ((weightedChaosCutoff M H N omega)
          ((centeredCube (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 4))
            (by positivity)) : Set (SpatialCoordinates d))).toReal)
        Filter.atTop (nhds L) := by
    rw [ae_all_iff]
    intro n
    exact SubdiffusiveProcess.chaos_cube_ae_tendsto hd M H hH _ _ _
  filter_upwards [h1, h2] with omega ha hb
  exact ⟨ha, hb⟩

end SubdiffusiveProcess.Paper
