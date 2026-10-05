module

public import Mathlib
public import SubdiffusiveProcess.Sobolev.WeakGradient
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.Section10.TransitionPositiveTests
public import SubdiffusiveProcess.Section10.TransitionPassage
public import MarkovProcess.Path.Exhaustion
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- Section 10, paper label `lim:lem-transition-domination`.  -/
theorem aux_lim_transition_domination_killed_integral
    {d : ℕ} (P : Measure (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : C(SpatialCoordinates d, ℝ)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂((P.restrict
      {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}).map
      (fun w : DiffusionPath d => w t))) =
    ∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0) ∂P := by
  have hS : MeasurableSet {w : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U w} :=
    (aux_lim_transition_domination_survival_open U hU t).measurableSet
  have hg : Measurable (fun w : DiffusionPath d => w t) := (continuous_eval_const t).measurable
  have hf : Measurable (fun x : SpatialCoordinates d => ENNReal.ofReal (f x)) :=
    ENNReal.continuous_ofReal.measurable.comp f.continuous.measurable
  rw [MeasureTheory.lintegral_map hf hg]
  have hcongr : (fun w : DiffusionPath d =>
        ENNReal.ofReal (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0))
      = fun w : DiffusionPath d =>
        {w : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}.indicator
          (fun w => ENNReal.ofReal (f (w t))) w := by
    funext w
    by_cases h : (t : ℝ≥0∞) < ContinuousPath.exitTime U w
    · simp only [h, ite_true, Set.indicator_apply, mem_ofPred_eq]
    · simp only [h, ite_false, Set.indicator_apply, mem_ofPred_eq, ENNReal.ofReal_zero]
  rw [hcongr, MeasureTheory.lintegral_indicator hS]

/-- Section 10, paper label `lim:lem-transition-domination`.  -/
theorem aux_lim_transition_domination_killed_supported
    {d : ℕ} (P : Measure (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ≥0) :
    (((P.restrict {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}).map
      (fun w : DiffusionPath d => w t)).restrict U) =
    (P.restrict {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}).map
      (fun w : DiffusionPath d => w t) := by
  apply Measure.restrict_eq_self_of_ae_mem
  refine (MeasureTheory.ae_map_iff (f := fun w : DiffusionPath d => w t) ?_ hU.measurableSet).2 ?_
  · exact (continuous_eval_const (F := DiffusionPath d) (X := SpatialCoordinates d) t).measurable.aemeasurable
  · apply (ae_restrict_mem
      (aux_lim_transition_domination_survival_open U hU t).measurableSet).mono
    intro w hw
    exact ContinuousPath.mem_of_lt_exitTime U w t hw

/-- Section 10, paper label `lim:lem-transition-domination`.  -/
theorem aux_lim_transition_domination_vague_killed_passage
    {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (P : ProbabilityMeasure (DiffusionPath d))
    (PN : ℕ → ProbabilityMeasure (DiffusionPath d)) (hp : Tendsto PN atTop (𝓝 P))
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    (hmu : MeasuresConvergeLocally muN mu) (phi : ℕ → ℕ) (hphi : StrictMono phi) (C : ℝ)
    (hb : ∀ n, (∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
      ∂(PN (phi n) : Measure (DiffusionPath d))) ≤
        ENNReal.ofReal (C * ∫ x, f x ∂muN (phi n))) :
    (∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
      ∂(P : Measure (DiffusionPath d))) ≤ ENNReal.ofReal (C * ∫ x, f x ∂mu) := by
  have hconv_phi : Tendsto (fun n => PN (phi n)) atTop (𝓝 P) := hp.comp hphi.tendsto_atTop
  have hInt : Tendsto (fun n => ∫ x, f x ∂muN (phi n)) atTop (𝓝 (∫ x, f x ∂mu)) :=
    (hmu f).comp hphi.tendsto_atTop
  have hC : Tendsto (fun n => C * ∫ x, f x ∂muN (phi n)) atTop (𝓝 (C * ∫ x, f x ∂mu)) :=
    hInt.const_mul C
  have hb_tendsto : Tendsto (fun n => ENNReal.ofReal (C * ∫ x, f x ∂muN (phi n))) atTop
      (𝓝 (ENNReal.ofReal (C * ∫ x, f x ∂mu))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hC
  have hbound : ∀ n, ∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f.toContinuousMap (w t) else 0)
      ∂(PN (phi n) : Measure (DiffusionPath d)) ≤
        ENNReal.ofReal (C * ∫ x, f x ∂muN (phi n)) := fun n => hb n
  have hmain := aux_lim_transition_domination_killed_portmanteau_bound U hU t
    f.toContinuousMap (fun x => hf x) P (fun n => PN (phi n)) hconv_phi
    (fun n => ENNReal.ofReal (C * ∫ x, f x ∂muN (phi n)))
    (ENNReal.ofReal (C * ∫ x, f x ∂mu)) hb_tendsto hbound
  convert hmain using 2

/-- : weak path convergence and vague speed convergence pass a fixed-subsequence
    killed bound to absolute continuity, without any killed-path convergence assertion. -/
theorem aux_lim_transition_domination_killed_ac_of_subsequence
    {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ≥0)
    (P : ProbabilityMeasure (DiffusionPath d))
    (PN : ℕ → ProbabilityMeasure (DiffusionPath d)) (hp : Tendsto PN atTop (𝓝 P))
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    [IsLocallyFiniteMeasure mu] (hmu : MeasuresConvergeLocally muN mu)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (f : C_c(SpatialCoordinates d, ℝ)), (∀ x, 0 ≤ f x) → tsupport f ⊆ U →
      ∀ n, (∫⁻ w, ENNReal.ofReal
        (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
        ∂(PN (phi n) : Measure (DiffusionPath d))) ≤
          ENNReal.ofReal (C * ∫ x, f x ∂muN (phi n))) :
    ((P : Measure (DiffusionPath d)).restrict
      {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}).map
      (fun w : DiffusionPath d => w t) ≪ mu := by
  apply aux_lim_transition_domination_ac_from_tests _ mu U hU
    (aux_lim_transition_domination_killed_supported _ U hU t) C hC
  intro f hf hfs
  exact (aux_lim_transition_domination_killed_integral (P : Measure (DiffusionPath d))
    U hU t f.toContinuousMap).trans_le
      (aux_lim_transition_domination_vague_killed_passage U hU t f hf P PN hp
        muN mu hmu phi hphi C (hb f hf hfs))

/-- : any tail of the deterministic spatial exhaustion still covers every finite path segment. -/
theorem aux_lim_transition_domination_shifted_survival_exhaustion
    {d : ℕ} (N0 : ℕ) (w : DiffusionPath d) (t : ℝ≥0) :
    ∃ n : ℕ, (t : ℝ≥0∞) < ContinuousPath.exitTime
      (Metric.ball (0 : SpatialCoordinates d) (((N0 + n : ℕ) : ℝ) + 1)) w := by
  obtain ⟨n, hn⟩ := aux_lim_transition_domination_survival_exhaustion w t
  refine ⟨n, hn.trans_le (ContinuousPath.exitTime_mono (Metric.ball_subset_ball ?_) w)⟩
  have hle : (n : ℝ) ≤ ((N0 + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left n N0
  linarith

/-- : killed absolute continuity on the tail of the exhaustion implies full marginal AC. -/
theorem aux_lim_transition_domination_ac_of_killed_tail
    {d : ℕ} (P : Measure (DiffusionPath d)) (mu : Measure (SpatialCoordinates d))
    (t : ℝ≥0) (N0 : ℕ)
    (hac : ∀ n : ℕ, N0 ≤ n →
      (P.restrict {w | (t : ℝ≥0∞) < ContinuousPath.exitTime
        (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) w}).map
        (fun w : DiffusionPath d => w t) ≪ mu) :
    P.map (fun w : DiffusionPath d => w t) ≪ mu := by
  apply aux_lim_transition_domination_exhaustion_ac P mu (fun w : DiffusionPath d => w t)
    (continuous_eval_const t).measurable
    (fun n => {w | (t : ℝ≥0∞) < ContinuousPath.exitTime
      (Metric.ball (0 : SpatialCoordinates d) (((N0 + n : ℕ) : ℝ) + 1)) w})
  · intro n
    exact (aux_lim_transition_domination_survival_open _ Metric.isOpen_ball t).measurableSet
  · apply Set.eq_univ_of_forall
    intro w
    obtain ⟨n, hn⟩ := aux_lim_transition_domination_shifted_survival_exhaustion N0 w t
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · intro n
    exact hac (N0 + n) (Nat.le_add_right N0 n)

end SubdiffusiveProcess.Paper
