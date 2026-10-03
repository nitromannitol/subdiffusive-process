module

public import SubdiffusiveProcess.Paper.limit_kernel_path_limit
public import SubdiffusiveProcess.Paper.resolvent_datum
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.lem_tightness_deterministic_restart


@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_limit_kernel_markov_passage_cutoff_attachment
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d →
      SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
      (DiffusionPath d))
    (hin : in_crossing M H PN KN) :
    (∀ N omega, (PN N omega).IsConservative) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) := by
  unfold in_crossing at hin
  exact ⟨hin.2.1, hin.2.2⟩

theorem aux_limit_kernel_markov_passage_cutoff_restart
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d →
      SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
      (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ x : SpatialCoordinates d, ∀ t : ℝ≥0,
        ∀ A : Set (DiffusionPath d),
          MeasurableSet[
            ContinuousPath.canonicalFiltration
              (alpha := SpatialCoordinates d) t] A →
            ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
              (∫⁻ path in A, F (ContinuousPath.shift t path)
                  ∂(KN N (omega, x))) =
                (∫⁻ path in A,
                  ∫⁻ future, F future ∂(KN N (omega, path t))
                    ∂(KN N (omega, x))) := by
  exact lem_tightness_deterministic_restart hd M H PN KN hKN hin

section MarkovPassageGeneric

open Metric Set BoundedContinuousFunction
open scoped BoundedContinuousFunction

/-- Lévy–Prokhorov convergence implies weak convergence of probability measures. -/
lemma aux_limit_kernel_markov_passage_tendsto_of_dist
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (h : ∀ ε > 0, ∀ᶠ k in atTop,
      dist (LevyProkhorov.ofMeasure (μs k)) (LevyProkhorov.ofMeasure μ) < ε) :
    Tendsto μs atTop (𝓝 μ) := by
  have h1 : Tendsto (fun k => LevyProkhorov.ofMeasure (μs k)) atTop
      (𝓝 (LevyProkhorov.ofMeasure μ)) := Metric.tendsto_nhds.2 h
  exact (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp h1

/-- Uniform convergence of integrals of one bounded continuous test function over a compact
set of parameters, from locally uniform Lévy–Prokhorov convergence to a continuous limit. -/
lemma aux_limit_kernel_markov_passage_integral_unif
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace.SeparableSpace X]
    {S : Type*} [TopologicalSpace S]
    (μs : ℕ → S → ProbabilityMeasure X) (μ : S → ProbabilityMeasure X)
    (hμ : Continuous μ) {B : Set S} (hB : IsCompact B)
    (hconv : ∀ ε > 0, ∀ᶠ k in atTop, ∀ y ∈ B,
      dist (LevyProkhorov.ofMeasure (μs k y)) (LevyProkhorov.ofMeasure (μ y)) < ε)
    (G : X →ᵇ ℝ) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ y ∈ B,
      |∫ p, G p ∂(μs k y : Measure X) - ∫ p, G p ∂(μ y : Measure X)| < ε := by
  intro ε hε
  set Φ : LevyProkhorov (ProbabilityMeasure X) → ℝ :=
    fun m => ∫ p, G p ∂(m.toMeasure : Measure X) with hΦ
  have hΦc : Continuous Φ := by
    have h1 : Continuous fun m : ProbabilityMeasure X => ∫ p, G p ∂(m : Measure X) :=
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction G
    exact h1.comp LevyProkhorov.continuous_toMeasure_probabilityMeasure
  have hC : IsCompact ((fun y => LevyProkhorov.ofMeasure (μ y)) '' B) :=
    hB.image (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp hμ)
  have hU := hC.uniformContinuousAt_of_continuousAt Φ
    (fun a _ => hΦc.continuousAt) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_uniformity_dist.1 hU
  filter_upwards [hconv δ hδ] with k hk y hy
  have h2 := hδU (a := LevyProkhorov.ofMeasure (μ y)) (b := LevyProkhorov.ofMeasure (μs k y))
    (by rw [dist_comm]; exact hk y hy) ⟨y, hy, rfl⟩
  have h3 : dist (Φ (LevyProkhorov.ofMeasure (μ y))) (Φ (LevyProkhorov.ofMeasure (μs k y))) < ε :=
    h2
  rw [Real.dist_eq, abs_sub_comm] at h3
  exact h3

/-- Weak convergence of the laws plus locally uniform convergence of uniformly bounded
integrands to a bounded continuous limit gives convergence of the integrals (compact-tail
truncation). -/
lemma aux_limit_kernel_markov_passage_tendsto_integral_of_locUnif
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    (s0 : S) {νs : ℕ → ProbabilityMeasure S} {ν : ProbabilityMeasure S}
    (hν : Tendsto νs atTop (𝓝 ν))
    (φs : ℕ → S → ℝ) (hφm : ∀ k, AEStronglyMeasurable (φs k) (νs k : Measure S)) {C : ℝ}
    (hφb : ∀ k y, |φs k y| ≤ C) (φ : S →ᵇ ℝ)
    (hunif : ∀ R : ℝ, ∀ ε > 0, ∀ᶠ k in atTop, ∀ y ∈ closedBall s0 R, |φs k y - φ y| < ε) :
    Tendsto (fun k => ∫ y, φs k y ∂(νs k : Measure S)) atTop
      (𝓝 (∫ y, φ y ∂(ν : Measure S))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set D : ℝ := C + ‖φ‖ with hD
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hφb 0 s0)
  have hD0 : 0 ≤ D := add_nonneg hC0 (norm_nonneg _)
  set η : ℝ := ε / (2 * (1 + D)) with hη
  have hηpos : 0 < η := by positivity
  have hηε : η * (1 + D) = ε / 2 := by
    rw [hη]; field_simp
  -- a ball carrying all but `η` of the limit law
  have hball : ∃ n : ℕ, (ν : Measure S) (ball s0 n)ᶜ < ENNReal.ofReal η := by
    have hanti : Antitone fun n : ℕ => (ball s0 (n : ℝ))ᶜ := by
      intro a b hab
      exact compl_subset_compl.2 (ball_subset_ball (by exact_mod_cast hab))
    have hlim := tendsto_measure_iInter_atTop (μ := (ν : Measure S))
      (fun n => (isOpen_ball.isClosed_compl).measurableSet.nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, (ball s0 (n : ℝ))ᶜ) = ∅ := by
      ext y
      simp only [mem_iInter, mem_compl_iff, mem_ball, not_lt, mem_empty_iff_false, iff_false,
        not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (dist y s0)
      exact ⟨n, hn⟩
    rw [hempty, measure_empty] at hlim
    exact ((tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 hηpos)).exists
  obtain ⟨n, hn⟩ := hball
  set F : Set S := (ball s0 (n : ℝ))ᶜ with hF
  have hFc : IsClosed F := isOpen_ball.isClosed_compl
  have hFm : MeasurableSet F := hFc.measurableSet
  have htail : ∀ᶠ k in atTop, (νs k : Measure S) F < ENNReal.ofReal η := by
    have hls := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hν hFc
    exact eventually_lt_of_limsup_lt (lt_of_le_of_lt hls hn) (by isBoundedDefault)
  have hweak := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν φ)
  rw [Metric.tendsto_nhds] at hweak
  filter_upwards [htail, hunif n η hηpos, hweak (ε / 2) (by positivity)] with k hk1 hk2 hk3
  have hint1 : Integrable (φs k) (νs k : Measure S) :=
    Integrable.of_bound (hφm k) C (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hφb k y)
  have hint2 : Integrable (fun y => φ y) (νs k : Measure S) := φ.integrable _
  have hpt : ∀ y, |φs k y - φ y| ≤ η + D * F.indicator (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ F
    · rw [indicator_of_mem hy, mul_one]
      have h1 : |φs k y - φ y| ≤ |φs k y| + |φ y| := abs_sub _ _
      have h2 : |φ y| ≤ ‖φ‖ := by
        rw [← Real.norm_eq_abs]; exact φ.norm_coe_le_norm y
      have := hφb k y
      linarith
    · rw [indicator_of_notMem hy, mul_zero, add_zero]
      have hyb : y ∈ closedBall s0 (n : ℝ) := by
        simp only [hF, mem_compl_iff, not_not] at hy
        exact ball_subset_closedBall hy
      exact (hk2 y hyb).le
  have hbound : |∫ y, φs k y ∂(νs k : Measure S) - ∫ y, φ y ∂(νs k : Measure S)| ≤
      η + D * ((νs k : Measure S) F).toReal := by
    rw [← integral_sub hint1 hint2]
    refine (abs_integral_le_integral_abs).trans ?_
    have hint3 : Integrable (fun y => η + D * F.indicator (fun _ => (1 : ℝ)) y)
        (νs k : Measure S) :=
      (integrable_const η).add ((integrable_const (1 : ℝ)).indicator hFm |>.const_mul D)
    refine (integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hint3
      (Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_add (integrable_const η) ((integrable_const (1 : ℝ)).indicator hFm |>.const_mul D),
      integral_const_mul, integral_indicator_const _ hFm]
    simp [Measure.real]
  have htoReal : ((νs k : Measure S) F).toReal < η :=
    ENNReal.toReal_lt_of_lt_ofReal hk1
  have h3 : |∫ y, φ y ∂(νs k : Measure S) - ∫ y, φ y ∂(ν : Measure S)| < ε / 2 := by
    rw [← Real.dist_eq]; exact hk3
  rw [Real.dist_eq]
  calc |∫ y, φs k y ∂(νs k : Measure S) - ∫ y, φ y ∂(ν : Measure S)|
      ≤ |∫ y, φs k y ∂(νs k : Measure S) - ∫ y, φ y ∂(νs k : Measure S)| +
        |∫ y, φ y ∂(νs k : Measure S) - ∫ y, φ y ∂(ν : Measure S)| := abs_sub_le _ _ _
    _ < (η + D * η) + ε / 2 := by
        have : D * ((νs k : Measure S) F).toReal ≤ D * η :=
          mul_le_mul_of_nonneg_left htoReal.le hD0
        linarith
    _ = ε := by nlinarith [hηε]

/-- The probability-measure view of a Markov kernel at a point. -/
def aux_limit_kernel_markov_passage_pm {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    (κ : Kernel S X) [IsMarkovKernel κ] (y : S) : ProbabilityMeasure X :=
  ⟨κ y, inferInstance⟩

/-- The deterministic-time restart identity, tested against products of bounded continuous
functions, passes from locally uniformly convergent Markov kernels to a limit kernel that is
continuous in the starting point. -/
lemma aux_limit_kernel_markov_passage_restart_limit
    {S : Type*} [PseudoMetricSpace S] [ProperSpace S] [MeasurableSpace S] [BorelSpace S]
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace.SeparableSpace X]
    (κs : ℕ → Kernel S X) [∀ k, IsMarkovKernel (κs k)] (κ : Kernel S X) [IsMarkovKernel κ]
    (hcont : Continuous (aux_limit_kernel_markov_passage_pm κ))
    (hconv : ∀ B : Set S, IsCompact B → ∀ ε > 0, ∀ᶠ k in atTop, ∀ y ∈ B,
      dist (LevyProkhorov.ofMeasure (aux_limit_kernel_markov_passage_pm (κs k) y))
        (LevyProkhorov.ofMeasure (aux_limit_kernel_markov_passage_pm κ y)) < ε)
    {e : X → S} (he : Continuous e) {σ : X → X} (hσ : Continuous σ)
    (hs : ∀ k x (f : S →ᵇ ℝ) (G : X →ᵇ ℝ),
      ∫ p, f (e p) * G (σ p) ∂(κs k x) = ∫ p, f (e p) * (∫ q, G q ∂(κs k (e p))) ∂(κs k x))
    (x : S) (f : S →ᵇ ℝ) (G : X →ᵇ ℝ) :
    ∫ p, f (e p) * G (σ p) ∂(κ x) = ∫ p, f (e p) * (∫ q, G q ∂(κ (e p))) ∂(κ x) := by
  set pm := @aux_limit_kernel_markov_passage_pm S X _ _ with hpm
  have hx : Tendsto (fun k => pm (κs k) x) atTop (𝓝 (pm κ x)) := by
    apply aux_limit_kernel_markov_passage_tendsto_of_dist
    intro ε hε
    filter_upwards [hconv {x} isCompact_singleton ε hε] with k hk
    exact hk x rfl
  -- the left side converges by weak convergence at the fixed start
  set T : X →ᵇ ℝ := (f.compContinuous ⟨e, he⟩) * (G.compContinuous ⟨σ, hσ⟩) with hT
  have hL : Tendsto (fun k => ∫ p, f (e p) * G (σ p) ∂(κs k x)) atTop
      (𝓝 (∫ p, f (e p) * G (σ p) ∂(κ x))) := by
    have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hx T
    simpa [T, pm, aux_limit_kernel_markov_passage_pm] using this
  -- the right side: compact-tail truncation of the time marginal
  set h : S → ℝ := fun y => ∫ q, G q ∂(κ y) with hh
  have hhc : Continuous h :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).comp hcont
  have hhb : ∀ y, ‖h y‖ ≤ ‖G‖ := fun y => by
    have := norm_integral_le_of_norm_le_const (μ := κ y) (C := ‖G‖)
      (Eventually.of_forall fun q => G.norm_coe_le_norm q)
    simpa [h, Measure.real] using this
  set hb : S →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup h hhc ‖G‖ hhb with hhbdef
  set νs : ℕ → ProbabilityMeasure S := fun k => (pm (κs k) x).map e
    with hνs
  set ν : ProbabilityMeasure S := (pm κ x).map e with hν
  have hνt : Tendsto νs atTop (𝓝 ν) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hx he
  have hunif : ∀ R : ℝ, ∀ ε > 0, ∀ᶠ k in atTop, ∀ y ∈ closedBall x R,
      |f y * (∫ q, G q ∂(κs k y)) - (f * hb) y| < ε := by
    intro R ε hε
    have hε' : 0 < ε / (‖f‖ + 1) := by positivity
    have hA := aux_limit_kernel_markov_passage_integral_unif (fun k y => pm (κs k) y) (pm κ)
      hcont (isCompact_closedBall x R) (hconv _ (isCompact_closedBall x R)) G _ hε'
    filter_upwards [hA] with k hk y hy
    have h1 := hk y hy
    have h2 : |f y| ≤ ‖f‖ := by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm y
    have h3 : |∫ q, G q ∂(κs k y) - h y| < ε / (‖f‖ + 1) := h1
    have heq : f y * (∫ q, G q ∂(κs k y)) - (f * hb) y = f y * ((∫ q, G q ∂(κs k y)) - h y) := by
      simp [hb, h]; ring
    rw [heq, abs_mul]
    calc |f y| * |∫ q, G q ∂(κs k y) - h y| ≤ ‖f‖ * |∫ q, G q ∂(κs k y) - h y| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ ≤ ‖f‖ * (ε / (‖f‖ + 1)) := mul_le_mul_of_nonneg_left h3.le (norm_nonneg _)
      _ < ε := by
          rw [mul_div_assoc']
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg f]
  have hsm : ∀ k, StronglyMeasurable (fun y => f y * ∫ q, G q ∂(κs k y)) := fun k =>
    f.continuous.stronglyMeasurable.mul
      (G.continuous.stronglyMeasurable.integral_kernel (κ := κs k))
  have hmeas : ∀ k, AEStronglyMeasurable (fun y => f y * ∫ q, G q ∂(κs k y))
      (νs k : Measure S) := fun k => (hsm k).aestronglyMeasurable
  have hbound : ∀ k y, |f y * ∫ q, G q ∂(κs k y)| ≤ ‖f‖ * ‖G‖ := by
    intro k y
    rw [abs_mul]
    have h2 : |f y| ≤ ‖f‖ := by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm y
    have h4 : |∫ q, G q ∂(κs k y)| ≤ ‖G‖ := by
      have := norm_integral_le_of_norm_le_const (μ := κs k y) (C := ‖G‖)
        (Eventually.of_forall fun q => G.norm_coe_le_norm q)
      rw [← Real.norm_eq_abs]
      simpa [Measure.real] using this
    exact mul_le_mul h2 h4 (abs_nonneg _) (norm_nonneg _)
  have hR := aux_limit_kernel_markov_passage_tendsto_integral_of_locUnif x hνt
    (fun k y => f y * ∫ q, G q ∂(κs k y)) hmeas hbound (f * hb) hunif
  -- rewrite the time-marginal integrals as path integrals
  have hmapN : ∀ k, ∫ y, f y * (∫ q, G q ∂(κs k y)) ∂(νs k : Measure S) =
      ∫ p, f (e p) * (∫ q, G q ∂(κs k (e p))) ∂(κs k x) := by
    intro k
    rw [show (νs k : Measure S) = (κs k x).map e from
      ProbabilityMeasure.toMeasure_map _]
    exact integral_map he.measurable.aemeasurable (hsm k).aestronglyMeasurable
  have hmap : ∫ y, (f * hb) y ∂(ν : Measure S) =
      ∫ p, f (e p) * (∫ q, G q ∂(κ (e p))) ∂(κ x) := by
    rw [show (ν : Measure S) = (κ x).map e from ProbabilityMeasure.toMeasure_map _]
    rw [integral_map he.measurable.aemeasurable (f * hb).continuous.aestronglyMeasurable]
    simp [hb, h]
  have hR' : Tendsto (fun k => ∫ p, f (e p) * G (σ p) ∂(κs k x)) atTop
      (𝓝 (∫ p, f (e p) * (∫ q, G q ∂(κ (e p))) ∂(κ x))) := by
    rw [← hmap]
    refine hR.congr fun k => ?_
    rw [hmapN k, hs k x f G]
  exact tendsto_nhds_unique hL hR'

end MarkovPassageGeneric

section MarkovPassageSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]

lemma aux_limit_kernel_markov_passage_measurable_eval (t : ℝ≥0) :
    Measurable (fun p : ContinuousPath α => p t) :=
  (continuous_eval_const t).measurable

omit [MeasurableSpace α] [BorelSpace α] in
lemma aux_limit_kernel_markov_passage_measurable_shift (t : ℝ≥0) :
    Measurable (ContinuousPath.shift t : ContinuousPath α → ContinuousPath α) :=
  (ContinuousPath.continuous_shift_fixed t).measurable

lemma aux_limit_kernel_markov_passage_measurable_evalShift (t : ℝ≥0) :
    Measurable (fun p : ContinuousPath α => (p t, ContinuousPath.shift t p)) :=
  (aux_limit_kernel_markov_passage_measurable_eval t).prodMk
    (aux_limit_kernel_markov_passage_measurable_shift t)

omit [TopologicalSpace α] [BorelSpace α] in
/-- Composition-product with a kernel that ignores the first coordinate. -/
lemma aux_limit_kernel_markov_passage_compProd_prodMkLeft_apply
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (κ₁ : Kernel α β) [IsSFiniteKernel κ₁] (η : Kernel β γ) [IsSFiniteKernel η] (x : α) :
    (κ₁ ⊗ₖ Kernel.prodMkLeft α η) x = (κ₁ x) ⊗ₘ η := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  simp only [Kernel.prodMkLeft_apply]

/-- The marginal-transition semigroup of a path kernel with the deterministic-time restart
property and the correct starting point. -/
def aux_limit_kernel_markov_passage_marginalSemigroup
    (κ : Kernel α (ContinuousPath α)) [IsMarkovKernel κ]
    (hzero : ∀ x, (κ x).map (fun p => p 0) = Measure.dirac x)
    (hrestart : ∀ x t, (κ x).map (fun p => (p t, ContinuousPath.shift t p)) =
      ((κ x).map (fun p => p t)) ⊗ₘ κ) :
    SubMarkovKernelSemigroup α where
  kernel t := κ.map (fun p => p t)
  measurable_kernel := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hT : MeasurableSet {z : (ℝ≥0 × α) × ContinuousPath α | z.2 z.1.1 ∈ s} := by
      have hm : Measurable (fun z : (ℝ≥0 × α) × ContinuousPath α => z.2 z.1.1) :=
        continuous_eval.measurable.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
      exact hm hs
    have h := Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkLeft ℝ≥0 κ) hT
    convert h using 1
    funext z
    simp only [Kernel.prodMkLeft_apply]
    rw [Kernel.map_apply _ (aux_limit_kernel_markov_passage_measurable_eval z.1),
      Measure.map_apply (aux_limit_kernel_markov_passage_measurable_eval z.1) hs]
    rfl
  kernel_zero := by
    ext1 x
    rw [Kernel.map_apply _ (aux_limit_kernel_markov_passage_measurable_eval 0), hzero x,
      Kernel.id_apply]
  kernel_add s t := by
    ext1 x
    rw [Kernel.comp_apply, Kernel.map_apply _ (aux_limit_kernel_markov_passage_measurable_eval _),
      Kernel.map_apply _ (aux_limit_kernel_markov_passage_measurable_eval _)]
    have h := congrArg (fun m : Measure (α × ContinuousPath α) => m.map (fun q => q.2 t))
      (hrestart x s)
    have hm2 : Measurable (fun q : α × ContinuousPath α => q.2 t) :=
      (aux_limit_kernel_markov_passage_measurable_eval t).comp measurable_snd
    rw [Measure.map_map hm2 (aux_limit_kernel_markov_passage_measurable_evalShift s)] at h
    have hfun : ((fun q : α × ContinuousPath α => q.2 t) ∘
        fun p : ContinuousPath α => (p s, ContinuousPath.shift s p)) = fun p => p (s + t) := by
      funext p; simp [ContinuousPath.shift_apply]
    rw [hfun] at h
    rw [h]
    have hsnd : (fun q : α × ContinuousPath α => q.2 t) =
        (fun p : ContinuousPath α => p t) ∘ Prod.snd := rfl
    rw [hsnd, ← Measure.map_map (aux_limit_kernel_markov_passage_measurable_eval t) measurable_snd]
    rw [show ((((κ x).map (fun p => p s)) ⊗ₘ κ).map Prod.snd) =
        (((κ x).map (fun p => p s)) ⊗ₘ κ).snd from rfl, Measure.snd_compProd,
      Measure.map_comp _ _ (aux_limit_kernel_markov_passage_measurable_eval t)]
  isSubMarkovKernel t := by
    haveI := Kernel.IsMarkovKernel.map κ (aux_limit_kernel_markov_passage_measurable_eval t)
    exact IsSubMarkovKernel.of_isMarkovKernel _

end MarkovPassageSemigroup

section MarkovPassageFDD

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
variable (κ : Kernel α (ContinuousPath α)) [IsMarkovKernel κ]
    (hzero : ∀ x, (κ x).map (fun p => p 0) = Measure.dirac x)
    (hrestart : ∀ x t, (κ x).map (fun p => (p t, ContinuousPath.shift t p)) =
      ((κ x).map (fun p => p t)) ⊗ₘ κ)

lemma aux_limit_kernel_markov_passage_marginalSemigroup_apply (t : ℝ≥0) (x : α) :
    (aux_limit_kernel_markov_passage_marginalSemigroup κ hzero hrestart) t x =
      (κ x).map (fun p => p t) := by
  change (κ.map (fun p : ContinuousPath α => p t)) x = _
  exact Kernel.map_apply _ (aux_limit_kernel_markov_passage_measurable_eval t) x

lemma aux_limit_kernel_markov_passage_marginalSemigroup_isConservative :
    (aux_limit_kernel_markov_passage_marginalSemigroup κ hzero hrestart).IsConservative := by
  intro t x
  rw [aux_limit_kernel_markov_passage_marginalSemigroup_apply,
    Measure.map_apply (aux_limit_kernel_markov_passage_measurable_eval t) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

/-- The ordered finite-time marginals of the path kernel are the finite-time kernels of its
marginal semigroup. -/
lemma aux_limit_kernel_markov_passage_finiteTimeKernel :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n) (x : α),
      (κ x).map (fun p : ContinuousPath α => fun i : Fin n => p (times i)) =
        SubMarkovKernelSemigroup.finiteTimeKernel
          (aux_limit_kernel_markov_passage_marginalSemigroup κ hzero hrestart) times x := by
  intro n
  induction n with
  | zero =>
    intro times x
    rw [SubMarkovKernelSemigroup.finiteTimeKernel_zero, Kernel.const_apply]
    have hf : (fun p : ContinuousPath α => fun i : Fin 0 => p (times i)) =
        fun _ => FiniteOrderedTimes.emptyPath α := by
      funext p; exact Subsingleton.elim _ _
    rw [hf, Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
    intro times x
    set P := aux_limit_kernel_markov_passage_marginalSemigroup κ hzero hrestart with hP
    set t0 := times 0 with ht0
    set rel := times.relativeTail with hrel
    have hmrel : Measurable (fun q : ContinuousPath α => fun i : Fin n => q (rel i)) :=
      Measurable.of_eval fun i => aux_limit_kernel_markov_passage_measurable_eval (rel i)
    have hcons := measurable_finCons (α := α) (n := n)
    have hfun : (fun p : ContinuousPath α => fun i : Fin (n + 1) => p (times i)) =
        (fun z : α × (Fin n → α) => @Fin.cons n (fun _ => α) z.1 z.2) ∘
          (Prod.map id (fun q : ContinuousPath α => fun i : Fin n => q (rel i))) ∘
          (fun p => (p t0, ContinuousPath.shift t0 p)) := by
      funext p i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [t0]
      · simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, Fin.cons_succ,
          ContinuousPath.shift_apply, rel, t0, FiniteOrderedTimes.add_relativeTail]
    have hkeq : κ.map (fun q : ContinuousPath α => fun i : Fin n => q (rel i)) =
        SubMarkovKernelSemigroup.finiteTimeKernel P rel := by
      ext1 y
      rw [Kernel.map_apply _ hmrel]
      exact ih rel y
    haveI : IsMarkovKernel (SubMarkovKernelSemigroup.finiteTimeKernel P rel) :=
      SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteTimeKernel P
        (aux_limit_kernel_markov_passage_marginalSemigroup_isConservative κ hzero hrestart) rel
    haveI : IsMarkovKernel (P t0) :=
      SubMarkovKernelSemigroup.IsConservative.isMarkovKernel
        (aux_limit_kernel_markov_passage_marginalSemigroup_isConservative κ hzero hrestart) t0
    have hpm : Measurable (Prod.map (id : α → α)
        (fun q : ContinuousPath α => fun i : Fin n => q (rel i))) :=
      measurable_id.prodMap hmrel
    rw [hfun, ← Measure.map_map hcons
        (hpm.comp (aux_limit_kernel_markov_passage_measurable_evalShift t0)),
      ← Measure.map_map hpm (aux_limit_kernel_markov_passage_measurable_evalShift t0),
      hrestart x t0, ← Measure.compProd_map hmrel, hkeq]
    rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
      Kernel.map_apply _ hcons, aux_limit_kernel_markov_passage_compProd_prodMkLeft_apply,
      aux_limit_kernel_markov_passage_marginalSemigroup_apply]

/-- The finite-set marginals of the path kernel are the finite-set kernels of its marginal
semigroup. -/
lemma aux_limit_kernel_markov_passage_map_finsetEvaluation (I : Finset ℝ≥0) (x : α) :
    (κ x).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel
        (aux_limit_kernel_markov_passage_marginalSemigroup κ hzero hrestart) I x := by
  have hmo := SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet (α := α) I
  have hmev : Measurable (fun p : ContinuousPath α =>
      fun i : Fin I.card => p (SubMarkovKernelSemigroup.finiteSetTimes I i)) :=
    Measurable.of_eval fun i =>
      aux_limit_kernel_markov_passage_measurable_eval (SubMarkovKernelSemigroup.finiteSetTimes I i)
  rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map, Kernel.map_apply _ hmo,
    ← aux_limit_kernel_markov_passage_finiteTimeKernel, Measure.map_map hmo hmev]
  congr 1
  funext p t
  simp only [Function.comp_apply, SubMarkovKernelSemigroup.orderedPathToFiniteSet,
    SubMarkovKernelSemigroup.finiteSetTimes, ContinuousPath.finiteEvaluation]
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

end MarkovPassageFDD

section MarkovPassageRestart

open BoundedContinuousFunction
open scoped BoundedContinuousFunction

/-- The lintegral form of the deterministic-time restart identity gives the joint law of the
time-`t` state and the shifted path. -/
lemma aux_limit_kernel_markov_passage_restart_measure_of_lintegral
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (κ : Kernel α (ContinuousPath α)) [IsMarkovKernel κ] (t : ℝ≥0) (x : α)
    (h : ∀ A : Set (ContinuousPath α),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t] A →
        ∀ F : ContinuousPath α → ℝ≥0∞, Measurable F →
          (∫⁻ p in A, F (ContinuousPath.shift t p) ∂(κ x)) =
            ∫⁻ p in A, ∫⁻ q, F q ∂(κ (p t)) ∂(κ x)) :
    (κ x).map (fun p => (p t, ContinuousPath.shift t p)) = ((κ x).map (fun p => p t)) ⊗ₘ κ := by
  have hΦ := aux_limit_kernel_markov_passage_measurable_evalShift (α := α) t
  have he := aux_limit_kernel_markov_passage_measurable_eval (α := α) t
  have hsh := aux_limit_kernel_markov_passage_measurable_shift (α := α) t
  haveI : IsProbabilityMeasure ((κ x).map (fun p => (p t, ContinuousPath.shift t p))) :=
    inferInstance
  refine Measure.ext_prod fun {B C} hB hC => ?_
  have hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      {p : ContinuousPath α | p t ∈ B} :=
    ContinuousPath.measurable_coordinateProcess_canonicalFiltration t hB
  have h1 := h _ hA (C.indicator 1) (measurable_one.indicator hC)
  have hl : (∫⁻ p in {p : ContinuousPath α | p t ∈ B},
      C.indicator 1 (ContinuousPath.shift t p) ∂(κ x)) =
      (κ x) ((fun p => (p t, ContinuousPath.shift t p)) ⁻¹' (B ×ˢ C)) := by
    have hfun : (fun p : ContinuousPath α => C.indicator (1 : ContinuousPath α → ℝ≥0∞)
        (ContinuousPath.shift t p)) = (ContinuousPath.shift t ⁻¹' C).indicator 1 := by
      funext p
      by_cases hp : ContinuousPath.shift t p ∈ C
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ ContinuousPath.shift t ⁻¹' C from hp)]
        rfl
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p ∉ ContinuousPath.shift t ⁻¹' C from hp)]
    rw [hfun, lintegral_indicator_one (hsh hC), Measure.restrict_apply (hsh hC)]
    congr 1
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod]
    exact and_comm
  have hr : (∫⁻ p in {p : ContinuousPath α | p t ∈ B},
      ∫⁻ q, C.indicator 1 q ∂(κ (p t)) ∂(κ x)) =
      ∫⁻ p in {p : ContinuousPath α | p t ∈ B}, κ (p t) C ∂(κ x) := by
    congr 1
    funext p
    exact lintegral_indicator_one hC
  rw [Measure.map_apply hΦ (hB.prod hC), Measure.compProd_apply_prod hB hC,
    setLIntegral_map hB (Kernel.measurable_coe κ hC) he, ← hl, h1, hr]
  rfl

variable {S X : Type*} [MeasurableSpace S] [TopologicalSpace S] [OpensMeasurableSpace S]
  [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

lemma aux_limit_kernel_markov_passage_integral_map_pair
    (κ : Kernel S X) [IsMarkovKernel κ] {e : X → S} (he : Measurable e)
    {σ : X → X} (hσ : Measurable σ) (x : S) (f : S →ᵇ ℝ) (G : X →ᵇ ℝ) :
    ∫ q, f q.1 * G q.2 ∂((κ x).map (fun p => (e p, σ p))) = ∫ p, f (e p) * G (σ p) ∂(κ x) := by
  have hm : Measurable (fun q : S × X => f q.1 * G q.2) :=
    (f.continuous.measurable.comp measurable_fst).mul (G.continuous.measurable.comp measurable_snd)
  rw [integral_map (he.prodMk hσ).aemeasurable hm.aestronglyMeasurable]

lemma aux_limit_kernel_markov_passage_integral_compProd_pair
    (κ : Kernel S X) [IsMarkovKernel κ] {e : X → S} (he : Measurable e)
    (x : S) (f : S →ᵇ ℝ) (G : X →ᵇ ℝ) :
    ∫ q, f q.1 * G q.2 ∂(((κ x).map e) ⊗ₘ κ) =
      ∫ p, f (e p) * (∫ q, G q ∂(κ (e p))) ∂(κ x) := by
  haveI : IsProbabilityMeasure ((κ x).map e) := inferInstance
  have hm : Measurable (fun q : S × X => f q.1 * G q.2) :=
    (f.continuous.measurable.comp measurable_fst).mul (G.continuous.measurable.comp measurable_snd)
  have hint : Integrable (fun q : S × X => f q.1 * G q.2) (((κ x).map e) ⊗ₘ κ) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (‖f‖ * ‖G‖)
      (Eventually.of_forall fun q => ?_)
    rw [norm_mul]
    exact mul_le_mul (f.norm_coe_le_norm _) (G.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  rw [Measure.integral_compProd hint]
  simp_rw [integral_const_mul]
  have hsm : StronglyMeasurable (fun y : S => f y * ∫ q, G q ∂(κ y)) :=
    f.continuous.stronglyMeasurable.mul (G.continuous.stronglyMeasurable.integral_kernel (κ := κ))
  rw [integral_map he.aemeasurable hsm.aestronglyMeasurable]

/-- The restart identity of measures gives the product-test identity. -/
lemma aux_limit_kernel_markov_passage_test_of_restart
    (κ : Kernel S X) [IsMarkovKernel κ] {e : X → S} (he : Measurable e)
    {σ : X → X} (hσ : Measurable σ) (x : S)
    (h : (κ x).map (fun p => (e p, σ p)) = ((κ x).map e) ⊗ₘ κ) (f : S →ᵇ ℝ) (G : X →ᵇ ℝ) :
    ∫ p, f (e p) * G (σ p) ∂(κ x) = ∫ p, f (e p) * (∫ q, G q ∂(κ (e p))) ∂(κ x) := by
  rw [← aux_limit_kernel_markov_passage_integral_map_pair κ he hσ x f G, h,
    aux_limit_kernel_markov_passage_integral_compProd_pair κ he x f G]

/-- The product-test identity determines the restart identity of measures. -/
lemma aux_limit_kernel_markov_passage_restart_of_test
    [BorelSpace S] [HasOuterApproxClosed S] [BorelSpace X] [HasOuterApproxClosed X]
    (κ : Kernel S X) [IsMarkovKernel κ] {e : X → S} (he : Measurable e)
    {σ : X → X} (hσ : Measurable σ) (x : S)
    (h : ∀ (f : S →ᵇ ℝ) (G : X →ᵇ ℝ),
      ∫ p, f (e p) * G (σ p) ∂(κ x) = ∫ p, f (e p) * (∫ q, G q ∂(κ (e p))) ∂(κ x)) :
    (κ x).map (fun p => (e p, σ p)) = ((κ x).map e) ⊗ₘ κ := by
  haveI : IsProbabilityMeasure ((κ x).map e) := inferInstance
  haveI : IsProbabilityMeasure ((κ x).map (fun p => (e p, σ p))) :=
    inferInstance
  refine Measure.ext_of_integral_mul_boundedContinuousFunction fun f G => ?_
  rw [aux_limit_kernel_markov_passage_integral_map_pair κ he hσ x f G,
    aux_limit_kernel_markov_passage_integral_compProd_pair κ he x f G]
  exact h f G

/-- The starting point passes to weak limits. -/
lemma aux_limit_kernel_markov_passage_start_limit
    [BorelSpace S] [HasOuterApproxClosed S] [MeasurableSingletonClass S]
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X} (hμ : Tendsto μs atTop (𝓝 μ))
    {e : X → S} (he : Continuous e) (x : S)
    (hstart : ∀ k, (μs k : Measure X).map e = Measure.dirac x) :
    (μ : Measure X).map e = Measure.dirac x := by
  haveI : IsProbabilityMeasure ((μ : Measure X).map e) :=
    inferInstance
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map he.measurable.aemeasurable f.continuous.aestronglyMeasurable, integral_dirac]
  have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ
    (f.compContinuous ⟨e, he⟩)
  have hconst : ∀ k, ∫ p, (f.compContinuous ⟨e, he⟩) p ∂(μs k : Measure X) = f x := by
    intro k
    have h1 := congrArg (fun m : Measure S => ∫ y, f y ∂m) (hstart k)
    rw [integral_map he.measurable.aemeasurable f.continuous.aestronglyMeasurable,
      integral_dirac] at h1
    simpa using h1
  simp_rw [hconst] at hlim
  simpa using tendsto_nhds_unique hlim tendsto_const_nhds

end MarkovPassageRestart


section MarkovPassageGood

/-- On one environment: a subsequence of cutoff kernels with the start and restart
identities, converging locally uniformly to a start-continuous kernel, forces the start and
restart identities for the limit. -/
theorem aux_limit_kernel_markov_passage_good {d : ℕ}
    (κs : ℕ → Kernel (SpatialCoordinates d) (DiffusionPath d)) [∀ k, IsMarkovKernel (κs k)]
    (κ : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel κ]
    (hcont : Continuous (aux_limit_kernel_markov_passage_pm κ))
    (hconv : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ ε > 0, ∀ᶠ k in atTop, ∀ y ∈ B,
      pathLevyProkhorovDist (aux_limit_kernel_markov_passage_pm (κs k) y)
        (aux_limit_kernel_markov_passage_pm κ y) < ε)
    (hstart : ∀ k x, (κs k x).map (fun p => p 0) = Measure.dirac x)
    (hrestart : ∀ k x (t : ℝ≥0) (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t] A →
        ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
          (∫⁻ p in A, F (ContinuousPath.shift t p) ∂(κs k x)) =
            ∫⁻ p in A, ∫⁻ q, F q ∂(κs k (p t)) ∂(κs k x)) :
    (∀ x, (κ x).map (fun p => p 0) = Measure.dirac x) ∧
      (∀ x (t : ℝ≥0), (κ x).map (fun p => (p t, ContinuousPath.shift t p)) =
        ((κ x).map (fun p => p t)) ⊗ₘ κ) := by
  letI : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  have hconv' : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ y ∈ B, dist (LevyProkhorov.ofMeasure (aux_limit_kernel_markov_passage_pm (κs k) y))
        (LevyProkhorov.ofMeasure (aux_limit_kernel_markov_passage_pm κ y)) < ε := hconv
  refine ⟨fun x => ?_, fun x t => ?_⟩
  · have hx : Tendsto (fun k => aux_limit_kernel_markov_passage_pm (κs k) x) atTop
        (𝓝 (aux_limit_kernel_markov_passage_pm κ x)) := by
      apply aux_limit_kernel_markov_passage_tendsto_of_dist
      intro ε hε
      filter_upwards [hconv' {x} isCompact_singleton ε hε] with k hk
      exact hk x rfl
    exact aux_limit_kernel_markov_passage_start_limit hx (continuous_eval_const 0) x
      (fun k => hstart k x)
  · have hevc : Continuous (fun p : DiffusionPath d => p t) := continuous_eval_const t
    have hshc : Continuous (ContinuousPath.shift t : DiffusionPath d → DiffusionPath d) :=
      ContinuousPath.continuous_shift_fixed t
    refine aux_limit_kernel_markov_passage_restart_of_test κ hevc.measurable hshc.measurable x ?_
    intro f G
    refine aux_limit_kernel_markov_passage_restart_limit κs κ hcont hconv' hevc hshc
      (fun k y f G => ?_) x f G
    exact aux_limit_kernel_markov_passage_test_of_restart (κs k) hevc.measurable
      hshc.measurable y
      (aux_limit_kernel_markov_passage_restart_measure_of_lintegral (κs k) t y
        (hrestart k y t)) f G

end MarkovPassageGood



theorem limit_kernel_markov_passage
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d →
      SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
      (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hKcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure K hK omega x))
    (hKconv : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
          (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                  (jointPathProbabilityMeasure K hK omega x)} ≤
            ENNReal.ofReal rho) :
    ∃ (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
      (_ : ∀ omega, (P omega).IsConservative),
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x := by
  classical
  set μ := (chaosSampleLaw M).toMeasure with hμ
  have hrestartN := aux_limit_kernel_markov_passage_cutoff_restart hd M H PN KN hKN hin
  obtain ⟨-, hattachN⟩ := aux_limit_kernel_markov_passage_cutoff_attachment M H PN KN hin
  -- a deterministic fast subsequence on the closed balls of radius `k`
  have hstep : ∀ k : ℕ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      μ {omega : BilateralField d | ∃ x ∈ Metric.closedBall (0 : SpatialCoordinates d) k,
        (1 / 2 : ℝ) ^ k ≤ pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x)} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
    fun k => hKconv _ (isCompact_closedBall _ _) _ (by positivity) _ (by positivity)
  choose n hn using hstep
  set E : ℕ → Set (BilateralField d) := fun k =>
    {omega : BilateralField d | ∃ x ∈ Metric.closedBall (0 : SpatialCoordinates d) k,
      (1 / 2 : ℝ) ^ k ≤ pathLevyProkhorovDist
        (jointPathProbabilityMeasure (KN (n k)) (hKN (n k)) omega x)
        (jointPathProbabilityMeasure K hK omega x)} with hE
  have hsum : ∑' k, μ (E k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ?_
      (ENNReal.tsum_le_tsum fun k => hn k (n k) le_rfl)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hBC : ∀ᵐ omega ∂μ, ∀ᶠ k in atTop, omega ∉ E k := ae_eventually_notMem hsum
  -- the limiting kernel on one environment
  let κ : BilateralField d → Kernel (SpatialCoordinates d) (DiffusionPath d) := fun omega =>
    K.comap (Prod.mk omega) measurable_prodMk_left
  haveI hκ : ∀ omega, IsMarkovKernel (κ omega) := fun omega =>
    ⟨fun x => hK.isProbabilityMeasure (omega, x)⟩
  let Q : BilateralField d → Prop := fun omega =>
    (∀ x, (κ omega x).map (fun p => p 0) = Measure.dirac x) ∧
      (∀ x (t : ℝ≥0), (κ omega x).map (fun p => (p t, ContinuousPath.shift t p)) =
        ((κ omega x).map (fun p => p t)) ⊗ₘ κ omega)
  have hQ : ∀ᵐ omega ∂μ, Q omega := by
    filter_upwards [hKcont, hrestartN, hattachN, hBC] with omega hc hr ha hb
    let κs : ℕ → Kernel (SpatialCoordinates d) (DiffusionPath d) := fun k =>
      (KN (n k)).comap (Prod.mk omega) measurable_prodMk_left
    haveI : ∀ k, IsMarkovKernel (κs k) := fun k =>
      ⟨fun x => (hKN (n k)).isProbabilityMeasure (omega, x)⟩
    refine aux_limit_kernel_markov_passage_good κs (κ omega) hc ?_ ?_ ?_
    · intro B hB ε hε
      obtain ⟨r, hr⟩ := hB.isBounded.subset_closedBall (0 : SpatialCoordinates d)
      obtain ⟨R, hR⟩ := exists_nat_ge r
      have hpow : ∀ᶠ k : ℕ in atTop, (1 / 2 : ℝ) ^ k < ε :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
          (gt_mem_nhds hε)
      filter_upwards [hb, hpow, eventually_ge_atTop R] with k hk1 hk2 hk3 y hy
      have hyk : y ∈ Metric.closedBall (0 : SpatialCoordinates d) k :=
        Metric.closedBall_subset_closedBall (hR.trans (by exact_mod_cast hk3)) (hr hy)
      have hlt : pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN (n k)) (hKN (n k)) omega y)
          (jointPathProbabilityMeasure K hK omega y) < (1 / 2 : ℝ) ^ k := by
        by_contra hge
        exact hk1 ⟨y, hyk, not_lt.1 hge⟩
      exact lt_trans hlt hk2
    · intro k x
      have hmev : Measurable (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d)
          ({0} : Finset ℝ≥0)) :=
        Measurable.of_eval fun t => (continuous_eval_const ((t : ℝ≥0))).measurable
      have h0 := map_eval_eq_of_finsetEvaluation (PN (n k) omega) (KN (n k) (omega, x)) x 0
        (by rw [← Kernel.map_apply _ hmev]; exact ha (n k) {0} x)
      rw [(PN (n k) omega).kernel_zero, Kernel.id_apply] at h0
      exact h0
    · intro k x t A hA F hF
      exact hr (n k) x t A hA F hF
  let P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d) := fun omega =>
    if h : Q omega then aux_limit_kernel_markov_passage_marginalSemigroup (κ omega) h.1 h.2
    else idSemigroup
  refine ⟨P, fun omega => ?_, ?_⟩
  · by_cases h : Q omega
    · simp only [P, dif_pos h]
      exact aux_limit_kernel_markov_passage_marginalSemigroup_isConservative _ _ _
    · simp only [P, dif_neg h]
      exact isConservative_idSemigroup
  · filter_upwards [hQ] with omega hω I x
    simp only [P, dif_pos hω]
    have hmev : Measurable (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) I) :=
      Measurable.of_eval fun t => (continuous_eval_const ((t : ℝ≥0))).measurable
    rw [Kernel.map_apply _ hmev]
    exact aux_limit_kernel_markov_passage_map_finsetEvaluation (κ omega) hω.1 hω.2 I x

end Paper

