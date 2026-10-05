module

public import Mathlib
public import SubdiffusiveProcess.Sobolev.WeakGradient
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.Path.ExitTime
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- Section 10, paper label `lim:lem-transition-domination`.  -/
theorem aux_lim_measure_vague_unique
    {d : ℕ} (muN : ℕ → Measure (SpatialCoordinates d))
    (mu nu : Measure (SpatialCoordinates d)) [mu.Regular] [nu.Regular]
    (hm : MeasuresConvergeLocally muN mu) (hn : MeasuresConvergeLocally muN nu) :
    mu = nu := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact tendsto_nhds_unique (hm f) (hn f)

theorem aux_lim_measure_vague_weight
    {d : ℕ} (muN : ℕ → Measure (SpatialCoordinates d))
    (mu : Measure (SpatialCoordinates d)) (hconv : MeasuresConvergeLocally muN mu)
    (g : C(SpatialCoordinates d, ℝ)) (hg : ∀ x, 0 ≤ g x) :
    MeasuresConvergeLocally
      (fun n => (muN n).withDensity (fun x => ENNReal.ofReal (g x)))
      (mu.withDensity (fun x => ENNReal.ofReal (g x))) := by
  intro f
  have hmeas : Measurable (fun x : SpatialCoordinates d => ENNReal.ofReal (g x)) :=
    ENNReal.continuous_ofReal.measurable.comp g.continuous.measurable
  have hint (nu : Measure (SpatialCoordinates d)) :
      (∫ x, f x ∂nu.withDensity (fun x => ENNReal.ofReal (g x))) =
        ∫ x, (g • f) x ∂nu := by
    rw [integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (⇑f)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [ENNReal.toReal_ofReal (hg x)]
    rfl
  simpa only [hint] using hconv (g • f)
/-- paper label `lim:lem-transition-domination`: an arbitrary Bochner-test limit is locally finite when its
    test integrals agree with a locally finite measure of full support. -/
theorem aux_lim_transition_domination_vague_local_finite
    {d : ℕ} (muN : ℕ → Measure (SpatialCoordinates d))
    (mu nu : Measure (SpatialCoordinates d)) [IsLocallyFiniteMeasure mu]
    [mu.IsOpenPosMeasure] (hm : MeasuresConvergeLocally muN mu)
    (hn : MeasuresConvergeLocally muN nu) : IsLocallyFiniteMeasure nu := by
  constructor
  intro x
  obtain ⟨f, hfone, hfc, _, hf⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (K := {x}) isCompact_singleton isOpen_univ (subset_univ _)
  let g : C_c(SpatialCoordinates d, ℝ) := ⟨f, hfc⟩
  have hgx : g x = 1 := hfone (mem_singleton x)
  have hpos : 0 < ∫ y, g y ∂mu :=
    g.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
      g.hasCompactSupport (fun y => (hf y).1) (by rw [hgx]; norm_num)
  have heq := tendsto_nhds_unique (hn g) (hm g)
  have hint : Integrable (fun y => g y) nu := by
    by_contra hh
    exact (heq.trans_ne (ne_of_gt hpos)) (integral_undef hh)
  refine ⟨{y | (1/2 : ℝ) < ‖g y‖}, ?_, hint.measure_norm_gt_lt_top (by norm_num)⟩
  apply (isOpen_lt continuous_const g.continuous.norm).mem_nhds
  change (1/2 : ℝ) < ‖g x‖
  rw [hgx]
  norm_num

/-- paper label `lim:lem-transition-domination`: no extra local-finiteness premise is needed for the
    arbitrary speed measure quantified by lim_transition_domination. -/
theorem aux_lim_transition_domination_vague_identification
    {d : ℕ} (muN : ℕ → Measure (SpatialCoordinates d))
    (mu nu : Measure (SpatialCoordinates d)) [IsLocallyFiniteMeasure mu]
    [mu.IsOpenPosMeasure] (hm : MeasuresConvergeLocally muN mu)
    (hn : MeasuresConvergeLocally muN nu) : nu = mu := by
  let := aux_lim_transition_domination_vague_local_finite muN mu nu hm hn
  exact Measure.ext_of_integral_eq_on_compactlySupported
    (fun f => tendsto_nhds_unique (hn f) (hm f))

end SubdiffusiveProcess.Paper
