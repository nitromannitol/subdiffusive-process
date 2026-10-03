module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The transfer of `eq:mfd-39` from the cutoffs to the limit, paper 4803-4805
("The bound for $\mu$ follows from the portmanteau theorem applied to open
balls").

A ball is OPEN, and vague convergence gives the portmanteau inequality in the
direction `mu U ≤ liminf mu_N U` for open `U` -- the direction that preserves an
upper bound is the other one, so the argument goes through the inner
regularity of `mu`: an open set's measure is approached from inside by
compactly supported test functions, each of which is integrated against
`mu_N` in the limit and is dominated by `mu_N U`.  That inner approximation is
carried as `hinner`; it holds for the limit produced by
Riesz-Markov-Kakutani, whose measure is a content measure and so inner regular
on open sets. -/
theorem chaos_limit_growth
    {d : ℕ} (epsilon K : ℝ) (hK : 0 ≤ K)
    (mu : Measure (SpatialCoordinates d))
    (muN : ℕ → Measure (SpatialCoordinates d))
    (hconv : MeasuresConvergeLocally muN mu)
    (hinner : ∀ U : Set (SpatialCoordinates d), IsOpen U → ∀ c : ℝ≥0∞, c < mu U →
      ∃ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
        tsupport f ⊆ U ∧ c < ENNReal.ofReal (∫ x, f x ∂mu))
    (Rset : Set (SpatialCoordinates d))
    (hbound : ∀ (N : ℕ) (x : SpatialCoordinates d), x ∈ Rset →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        muN N (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon))) :
    ∀ x ∈ Rset, ∀ r : ℝ, 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon)) := by
  classical
  intro x hx r hr hr1
  by_contra hcon
  push_neg at hcon
  obtain ⟨f, hf01, hfsupp, hflt⟩ :=
    hinner (Metric.ball x r) Metric.isOpen_ball _ hcon
  have hfzero : ∀ y, y ∉ Metric.ball x r → f y = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport ?_
    exact fun hmem => hy (hfsupp hmem)
  have hbd : ∀ N : ℕ, ∫ y, f y ∂(muN N) ≤ K * r ^ ((d : ℝ) - epsilon) := by
    intro N
    have hfinball : muN N (Metric.ball x r) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound N x hx r hr hr1)
    haveI : IsFiniteMeasure ((muN N).restrict (Metric.ball x r)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_ne le_top hfinball
    have hrestr : ∫ y, f y ∂(muN N)
        = ∫ y in Metric.ball x r, f y ∂(muN N) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hfzero).symm
    have hfmble : AEStronglyMeasurable (fun y => f y)
        ((muN N).restrict (Metric.ball x r)) :=
      (map_continuous f).aestronglyMeasurable
    have hfint : IntegrableOn (fun y => f y) (Metric.ball x r) (muN N) := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hfmble ?_
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (hf01 y).1]
        exact (hf01 y).2
    have hle1 : ∫ y in Metric.ball x r, f y ∂(muN N)
        ≤ ∫ _y in Metric.ball x r, (1 : ℝ) ∂(muN N) := by
      refine setIntegral_mono hfint (integrable_const (1 : ℝ)) ?_
      exact fun y => (hf01 y).2
    have hconst : ∫ _y in Metric.ball x r, (1 : ℝ) ∂(muN N)
        = (muN N (Metric.ball x r)).toReal := by
      simp [setIntegral_const, Measure.real]
    have htoreal : (muN N (Metric.ball x r)).toReal
        ≤ K * r ^ ((d : ℝ) - epsilon) := by
      have hb := hbound N x hx r hr hr1
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      rwa [ENNReal.toReal_ofReal (mul_nonneg hK (Real.rpow_nonneg hr.le _))] at this
    rw [hrestr]
    exact le_trans (le_trans hle1 (le_of_eq hconst)) htoreal
  have hlim : ∫ y, f y ∂mu ≤ K * r ^ ((d : ℝ) - epsilon) :=
    le_of_tendsto (hconv f) (Filter.Eventually.of_forall hbd)
  have hfinal : ENNReal.ofReal (∫ y, f y ∂mu)
      ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon)) :=
    ENNReal.ofReal_le_ofReal hlim
  exact absurd hflt (not_lt.mpr hfinal)

end Paper
