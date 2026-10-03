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
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.lem_determining
public import SubdiffusiveProcess.Paper.determining_functional_convergence
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Sequences

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section QuenchedConvergenceHelpers

open Set
open scoped BoundedContinuousFunction

/-! #### Capacity -/
/-- One step of the capacitability construction: cutting the `k`-th coordinate at a finite
bound loses arbitrarily little outer measure of the image. -/
theorem aux_prop_quenched_convergence_cut_step {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → α) (S : Set (ℕ → ℕ)) (k : ℕ)
    {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ b : ℕ, μ (f '' S) ≤ μ (f '' (S ∩ {s | s k ≤ b})) + η := by
  have hunion : f '' S = ⋃ b : ℕ, f '' (S ∩ {s | s k ≤ b}) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mem_iUnion.2 ⟨s k, s, ⟨hs, (le_rfl : s k ≤ s k)⟩, rfl⟩
    · intro hy
      obtain ⟨b, s, hs, rfl⟩ := mem_iUnion.1 hy
      exact ⟨s, hs.1, rfl⟩
  have hmono : Monotone (fun b : ℕ => f '' (S ∩ {s | s k ≤ b})) := by
    intro b b' hbb'
    exact image_mono (inter_subset_inter_right _ (fun s (hs : s k ≤ b) => le_trans hs hbb'))
  have hsup : μ (f '' S) = ⨆ b : ℕ, μ (f '' (S ∩ {s | s k ≤ b})) := by
    rw [hunion]
    exact hmono.measure_iUnion
  by_contra hcon
  push_neg at hcon
  have hfin : μ (f '' S) ≠ ∞ := measure_ne_top μ _
  have hpos : μ (f '' S) ≠ 0 := by
    have := hcon 0
    exact (lt_of_le_of_lt zero_le this).ne'
  have hle : μ (f '' S) ≤ μ (f '' S) - η := by
    conv_lhs => rw [hsup]
    refine iSup_le fun b => ?_
    exact ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top hfin
      (le_add_self.trans (hcon b).le)) (hcon b).le
  exact absurd hle (not_le.2 (ENNReal.sub_lt_self hfin hpos hη))

/-- The compactness step of capacitability: points in the closures of all truncated images
lie in the image of the limiting compact box. -/
theorem aux_prop_quenched_convergence_closure_box {α : Type*} [TopologicalSpace α] [T2Space α]
    [TopologicalSpace.PseudoMetrizableSpace α] (f : (ℕ → ℕ) → α) (hf : Continuous f)
    (m : ℕ → ℕ) (y : α)
    (hy : ∀ n : ℕ, y ∈ closure (f '' {s : ℕ → ℕ | ∀ i < n, s i ≤ m i})) :
    y ∈ f '' {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
  letI := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
  have hchoose : ∀ n : ℕ, ∃ s : ℕ → ℕ, (∀ i < n, s i ≤ m i) ∧
      dist (f s) y < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 (hy n) _ hpos
    obtain ⟨s, hs, rfl⟩ := hb
    exact ⟨s, hs, by rwa [dist_comm]⟩
  choose s hs hsd using hchoose
  let u : ℕ → ℕ → ℕ := fun n i => min (s n i) (m i)
  have hLc : IsCompact {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
    have : {s : ℕ → ℕ | ∀ i, s i ≤ m i} = Set.pi univ (fun i => Iic (m i)) := by
      ext s; simp only [mem_setOf_eq, Set.mem_pi, mem_univ, mem_Iic, true_implies]
    rw [this]
    exact isCompact_univ_pi fun i => (Set.finite_Iic (m i)).isCompact
  have huL : ∀ n, u n ∈ {s : ℕ → ℕ | ∀ i, s i ≤ m i} := fun n i => min_le_right _ _
  obtain ⟨a, haL, φ, hφ, hlim⟩ := hLc.tendsto_subseq huL
  have hslim : Tendsto (fun j => s (φ j)) atTop (𝓝 a) := by
    rw [tendsto_pi_nhds]
    intro i
    have hu_i : Tendsto (fun j => u (φ j) i) atTop (𝓝 (a i)) :=
      ((continuous_apply i).tendsto a).comp hlim
    refine hu_i.congr' ?_
    filter_upwards [eventually_ge_atTop (i + 1)] with j hj
    have hij : i < φ j := lt_of_lt_of_le (Nat.lt_of_succ_le hj) (hφ.id_le j)
    exact min_eq_left (hs (φ j) i hij)
  have hf1 : Tendsto (fun j => f (s (φ j))) atTop (𝓝 (f a)) :=
    (hf.tendsto a).comp hslim
  have hf2 : Tendsto (fun j => f (s (φ j))) atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) h0
    refine (hsd (φ j)).le.trans ?_
    have : (j : ℝ) ≤ φ j := by exact_mod_cast hφ.id_le j
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  exact ⟨a, haL, tendsto_nhds_unique hf1 hf2⟩

/-- Inner approximation of an analytic set by closed subsets, up to arbitrarily small outer
measure. -/
theorem aux_prop_quenched_convergence_analytic_inner {α : Type*} [TopologicalSpace α]
    [T2Space α] [TopologicalSpace.PseudoMetrizableSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : (ℕ → ℕ) → α) (hf : Continuous f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ L : Set α, IsClosed L ∧ L ⊆ range f ∧ μ (range f) ≤ μ L + ε := by
  classical
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε ℕ
  have hstep : ∀ (S : Set (ℕ → ℕ)) (k : ℕ), ∃ b : ℕ,
      μ (f '' S) ≤ μ (f '' (S ∩ {s | s k ≤ b})) + (ε' k : ℝ≥0∞) := fun S k =>
    aux_prop_quenched_convergence_cut_step μ f S k
      (by exact_mod_cast (hε'pos k).ne')
  choose bsel hbsel using hstep
  let D : ℕ → Set (ℕ → ℕ) := fun n =>
    Nat.rec (motive := fun _ => Set (ℕ → ℕ)) univ
      (fun k Dk => Dk ∩ {s | s k ≤ bsel Dk k}) n
  have hDsucc : ∀ k, D (k + 1) = D k ∩ {s | s k ≤ bsel (D k) k} := fun k => rfl
  let m : ℕ → ℕ := fun i => bsel (D i) i
  have hDeq : ∀ n, D n = {s : ℕ → ℕ | ∀ i < n, s i ≤ m i} := by
    intro n
    induction n with
    | zero => ext s; simp [D]
    | succ k ih =>
      rw [hDsucc, ih]
      ext s
      simp only [mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h1 i hi
        · simpa [m, ih] using h2
      · intro h
        refine ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), ?_⟩
        have := h k (Nat.lt_succ_self k)
        simpa [m, ih] using this
  have hbound : ∀ n, μ (range f) ≤ μ (f '' D n) + ∑ i ∈ Finset.range n, (ε' i : ℝ≥0∞) := by
    intro n
    induction n with
    | zero => simp [D, image_univ]
    | succ k ih =>
      rw [Finset.sum_range_succ, hDsucc]
      calc μ (range f) ≤ μ (f '' D k) + ∑ i ∈ Finset.range k, (ε' i : ℝ≥0∞) := ih
        _ ≤ (μ (f '' (D k ∩ {s | s k ≤ bsel (D k) k})) + (ε' k : ℝ≥0∞)) +
              ∑ i ∈ Finset.range k, (ε' i : ℝ≥0∞) := by gcongr; exact hbsel (D k) k
        _ = _ := by ring
  have hsum_le : ∀ n, ∑ i ∈ Finset.range n, (ε' i : ℝ≥0∞) ≤ ε := fun n =>
    (ENNReal.sum_le_tsum _).trans hε'sum.le
  let L : Set α := f '' {s : ℕ → ℕ | ∀ i, s i ≤ m i}
  have hLc : IsCompact {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
    have : {s : ℕ → ℕ | ∀ i, s i ≤ m i} = Set.pi univ (fun i => Iic (m i)) := by
      ext s; simp only [mem_setOf_eq, Set.mem_pi, mem_univ, mem_Iic, true_implies]
    rw [this]
    exact isCompact_univ_pi fun i => (Set.finite_Iic (m i)).isCompact
  have hLclosed : IsClosed L := (hLc.image hf).isClosed
  refine ⟨L, hLclosed, image_subset_range _ _, ?_⟩
  -- the closures of the truncated images decrease to a subset of `L`
  let C : ℕ → Set α := fun n => closure (f '' D n)
  have hCanti : Antitone C := by
    intro n n' hnn'
    refine closure_mono (image_mono ?_)
    rw [hDeq, hDeq]
    intro s hs i hi
    exact hs i (lt_of_lt_of_le hi hnn')
  have hCsub : (⋂ n, C n) ⊆ L := by
    intro y hy
    refine aux_prop_quenched_convergence_closure_box f hf m y (fun n => ?_)
    have := mem_iInter.1 hy n
    simpa [C, hDeq n] using this
  have hmeasC : μ (⋂ n, C n) = ⨅ n, μ (C n) :=
    hCanti.measure_iInter (fun n => isClosed_closure.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top μ _⟩
  calc μ (range f) ≤ ⨅ n, (μ (C n) + ε) := by
        refine le_iInf fun n => ?_
        calc μ (range f) ≤ μ (f '' D n) + ∑ i ∈ Finset.range n, (ε' i : ℝ≥0∞) := hbound n
          _ ≤ μ (C n) + ε := add_le_add (measure_mono subset_closure) (hsum_le n)
    _ = μ (⋂ n, C n) + ε := by rw [← ENNReal.iInf_add, hmeasC]
    _ ≤ μ L + ε := by gcongr

/-- **Analytic sets are null-measurable** for every finite Borel measure on a metrizable
Hausdorff space (the capacitability argument). -/
theorem aux_prop_quenched_convergence_analytic_nullMeasurable {α : Type*}
    [TopologicalSpace α] [T2Space α] [TopologicalSpace.PseudoMetrizableSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {A : Set α} (hA : AnalyticSet A) : NullMeasurableSet A μ := by
  rw [AnalyticSet_def] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact nullMeasurableSet_empty
  have hchoose : ∀ n : ℕ, ∃ L : Set α, IsClosed L ∧ L ⊆ range f ∧
      μ (range f) ≤ μ L + ((n : ℝ≥0∞) + 1)⁻¹ := fun n =>
    aux_prop_quenched_convergence_analytic_inner μ f hf (by simp)
  choose L hLc hLsub hLμ using hchoose
  let U : Set α := ⋃ n, L n
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun n => (hLc n).measurableSet
  have hUsub : U ⊆ range f := iUnion_subset hLsub
  have hle : μ (range f) ≤ μ U := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
    calc μ (range f) ≤ μ (L n) + ((n : ℝ≥0∞) + 1)⁻¹ := hLμ n
      _ ≤ μ U + ε := by
        gcongr
        · exact subset_iUnion L n
        · refine le_trans ?_ hn.le
          exact ENNReal.inv_le_inv.2 (le_self_add)
  have hdiff : μ (range f \ U) = 0 := by
    have hsplit := measure_inter_add_diff (range f) hUm (μ := μ)
    rw [inter_eq_right.2 hUsub] at hsplit
    have hfin : μ U ≠ ∞ := measure_ne_top μ _
    have : μ (range f \ U) ≤ 0 := by
      have h1 : μ U + μ (range f \ U) ≤ μ U + 0 := by
        rw [hsplit, add_zero]; exact hle
      exact (ENNReal.add_le_add_iff_left hfin).1 h1
    exact le_antisymm this zero_le
  have : range f = U ∪ (range f \ U) := (union_diff_cancel hUsub).symm
  rw [this]
  exact hUm.nullMeasurableSet.union (NullMeasurableSet.of_null hdiff)

/-- Markov's inequality for an uncountable-supremum event.  The event `∃ x ∈ B, c < F (ω, x)`
is the projection of a Borel set of a Polish product, hence analytic, hence null-measurable;
so its outer measure is controlled by the (lower) integral of the supremum. -/
theorem aux_prop_quenched_convergence_markov_sup {Ω X : Type*}
    [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω × X → ℝ≥0∞) (hF : Measurable F)
    (B : Set X) (hB : MeasurableSet B) (c : ℝ≥0∞) :
    c * μ {ω | ∃ x ∈ B, c < F (ω, x)} ≤ ∫⁻ ω, ⨆ x ∈ B, F (ω, x) ∂μ := by
  set A := {ω | ∃ x ∈ B, c < F (ω, x)} with hAdef
  have hS : MeasurableSet {p : Ω × X | p.2 ∈ B ∧ c < F p} :=
    (measurable_snd hB).inter (measurableSet_lt measurable_const hF)
  have hAeq : A = Prod.fst '' {p : Ω × X | p.2 ∈ B ∧ c < F p} := by
    ext ω; constructor
    · rintro ⟨x, hx, hc⟩; exact ⟨(ω, x), ⟨hx, hc⟩, rfl⟩
    · rintro ⟨⟨ω', x⟩, ⟨hx, hc⟩, rfl⟩; exact ⟨x, hx, hc⟩
  have hAan : AnalyticSet A := by
    rw [hAeq]; exact (hS.analyticSet).image_of_continuous continuous_fst
  have hAnull := aux_prop_quenched_convergence_analytic_nullMeasurable μ hAan
  obtain ⟨T, hTA, hTm, hTae⟩ := hAnull.exists_measurable_subset_ae_eq
  rw [← measure_congr hTae, ← lintegral_indicator_const hTm c]
  refine lintegral_mono fun ω => ?_
  by_cases hω : ω ∈ T
  · rw [indicator_of_mem hω]
    obtain ⟨x, hx, hc⟩ := hTA hω
    exact hc.le.trans (le_iSup₂ (f := fun x (_ : x ∈ B) => F (ω, x)) x hx)
  · rw [indicator_of_notMem hω]; exact zero_le

/-! #### Grid -/
/-- Time-grid control on a compact set of paths: closeness of two paths of `K` at the
(slightly perturbed) cumulative times of a fine uniform grid forces closeness in the path
metric.  The perturbation box `|s i - Δ| < κ` is what the discounted time integrals of the
determining functionals see. -/
theorem aux_prop_quenched_convergence_grid {X E : Type*} [MetricSpace X] [MetricSpace E]
    (ev : X → ℝ≥0 → E) (hev : Continuous (fun p : X × ℝ≥0 => ev p.1 p.2))
    (hinj : ∀ z z' : X, (∀ t, ev z t = ev z' t) → z = z')
    (K : Set X) (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ (k : ℕ) (Δ κ θ : ℝ), 0 < Δ ∧ 0 < κ ∧ κ < Δ ∧ 0 < θ ∧
      ∀ z ∈ K, ∀ z' ∈ K, ∀ s s' : Fin k → ℝ, (∀ i, |s i - Δ| < κ) →
        (∀ i, |s' i - Δ| < κ) →
        (∀ i : Fin k, dist (ev z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))
            (ev z' (Real.toNNReal (∑ j ∈ Finset.Iic i, s' j))) < θ) →
        dist z z' < r := by
  by_contra hcon
  push_neg at hcon
  let kk : ℕ → ℕ := fun n => (n + 1) ^ 2
  let Δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let κ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) ^ 4
  let θ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hΔ : ∀ n, 0 < Δ n := fun n => by positivity
  have hκ : ∀ n, 0 < κ n := fun n => by positivity
  have hκΔ : ∀ n, κ n < Δ n := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (n : ℝ) + 1 < ((n : ℝ) + 2) ^ 4 := by
      have h3 : (1 : ℝ) ≤ (n : ℝ) + 2 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      calc (n : ℝ) + 1 < (n : ℝ) + 2 := by linarith
        _ ≤ ((n : ℝ) + 2) ^ 4 := le_self_pow₀ h3 (by norm_num)
    exact one_div_lt_one_div_of_lt h1 h2
  have hθ : ∀ n, 0 < θ n := fun n => by positivity
  have H := fun n => hcon (kk n) (Δ n) (κ n) (θ n) (hΔ n) (hκ n) (hκΔ n) (hθ n)
  choose z hz z' hz' s s' hs hs' hclose hfar using H
  obtain ⟨⟨a, a'⟩, ha, φ, hφ, hlim⟩ :=
    IsCompact.tendsto_subseq (hK.prod hK) (x := fun n => (z n, z' n)) (fun n => ⟨hz n, hz' n⟩)
  have hlim1 : Tendsto (fun j => z (φ j)) atTop (𝓝 a) :=
    (continuous_fst.tendsto _).comp hlim
  have hlim2 : Tendsto (fun j => z' (φ j)) atTop (𝓝 a') :=
    (continuous_snd.tendsto _).comp hlim
  have hfar' : r ≤ dist a a' :=
    ge_of_tendsto (hlim1.dist hlim2) (Eventually.of_forall fun j => hfar (φ j))
  have hj0 : Tendsto (fun j : ℕ => 2 * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  have heq : a = a' := by
    apply hinj
    intro t
    let idx : ∀ n, Fin (kk n) := fun n =>
      ⟨min ⌊(t : ℝ) * ((n : ℝ) + 1)⌋₊ (kk n - 1), by
        have : 0 < kk n := by positivity
        omega⟩
    -- the cumulative time at the grid index nearest to `t`
    have htime : ∀ σ : ∀ n, Fin (kk n) → ℝ, (∀ n i, |σ n i - Δ n| < κ n) →
        Tendsto (fun j => Real.toNNReal (∑ i ∈ Finset.Iic (idx (φ j)), σ (φ j) i))
          atTop (𝓝 t) := by
      intro σ hσ
      have hreal : Tendsto (fun j => ∑ i ∈ Finset.Iic (idx (φ j)), σ (φ j) i)
          atTop (𝓝 (t : ℝ)) := by
        rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun j => dist_nonneg) ?_ hj0
        filter_upwards [eventually_ge_atTop ⌈(t : ℝ)⌉₊] with j hj
        set n := φ j with hn
        have hjn : (j : ℝ) ≤ n := by exact_mod_cast hφ.id_le j
        have htn : (t : ℝ) < (n : ℝ) + 1 := by
          have := Nat.le_ceil (t : ℝ)
          have : (⌈(t : ℝ)⌉₊ : ℝ) ≤ j := by exact_mod_cast hj
          linarith
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        set m := ⌊(t : ℝ) * ((n : ℝ) + 1)⌋₊ with hm
        have hm_le : (m : ℝ) ≤ (t : ℝ) * ((n : ℝ) + 1) :=
          Nat.floor_le (by positivity)
        have hm_lt : (t : ℝ) * ((n : ℝ) + 1) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
        have hm_small : m < kk n := by
          have : (t : ℝ) * ((n : ℝ) + 1) < ((n : ℝ) + 1) ^ 2 := by
            rw [sq]; exact mul_lt_mul_of_pos_right htn hn1
          have : (m : ℝ) < ((n + 1) ^ 2 : ℕ) := by push_cast; linarith
          exact_mod_cast this
        have hidx : ((idx n : Fin (kk n)) : ℕ) = m := by
          simp only [idx]
          exact min_eq_left (by omega)
        have hcard : ((Finset.Iic (idx n)).card : ℝ) = (m : ℝ) + 1 := by
          rw [Fin.card_Iic, hidx]; push_cast; ring
        -- deviation from the grid time
        have hdev : |∑ i ∈ Finset.Iic (idx n), σ n i - ((m : ℝ) + 1) * Δ n| ≤
            ((m : ℝ) + 1) * κ n := by
          have hsum : ∑ i ∈ Finset.Iic (idx n), σ n i - ((m : ℝ) + 1) * Δ n =
              ∑ i ∈ Finset.Iic (idx n), (σ n i - Δ n) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
          rw [hsum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine (Finset.sum_le_sum fun i _ => (hσ n i).le).trans ?_
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
        have hgrid : |((m : ℝ) + 1) * Δ n - t| ≤ Δ n := by
          have hΔn : Δ n = 1 / ((n : ℝ) + 1) := rfl
          rw [hΔn, abs_le]
          constructor
          · have : (t : ℝ) ≤ ((m : ℝ) + 1) / ((n : ℝ) + 1) := by
              rw [le_div_iff₀ hn1]; linarith
            have h' : ((m : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = ((m : ℝ) + 1) / ((n : ℝ) + 1) := by
              ring
            rw [h']
            have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
            linarith
          · have : ((m : ℝ) + 1) / ((n : ℝ) + 1) ≤ t + 1 / ((n : ℝ) + 1) := by
              rw [div_le_iff₀ hn1, add_mul, one_div_mul_cancel hn1.ne']; linarith
            have h' : ((m : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = ((m : ℝ) + 1) / ((n : ℝ) + 1) := by
              ring
            rw [h']; linarith
        have hmκ : ((m : ℝ) + 1) * κ n ≤ 1 / ((n : ℝ) + 1) := by
          have hmk : (m : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
            have : m + 1 ≤ kk n := hm_small
            have : ((m + 1 : ℕ) : ℝ) ≤ ((kk n : ℕ) : ℝ) := by exact_mod_cast this
            simpa [kk] using this
          have hκn : κ n = 1 / ((n : ℝ) + 2) ^ 4 := rfl
          rw [hκn]
          calc ((m : ℝ) + 1) * (1 / ((n : ℝ) + 2) ^ 4)
              ≤ ((n : ℝ) + 1) ^ 2 * (1 / ((n : ℝ) + 2) ^ 4) := by gcongr
            _ ≤ 1 / ((n : ℝ) + 1) := by
              rw [mul_one_div, div_le_div_iff₀ (by positivity) hn1]
              nlinarith [sq_nonneg ((n : ℝ) + 1), sq_nonneg ((n : ℝ) + 2)]
        rw [Real.dist_eq]
        calc |∑ i ∈ Finset.Iic (idx n), σ n i - t|
            ≤ |∑ i ∈ Finset.Iic (idx n), σ n i - ((m : ℝ) + 1) * Δ n| +
                |((m : ℝ) + 1) * Δ n - t| := abs_sub_le _ _ _
          _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
              have hΔn : Δ n = 1 / ((n : ℝ) + 1) := rfl
              linarith
          _ ≤ 2 * (1 / ((j : ℝ) + 1)) := by
              have : 1 / ((n : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
                one_div_le_one_div_of_le (by positivity) (by linarith)
              linarith
      have := (continuous_real_toNNReal.tendsto (t : ℝ)).comp hreal
      simpa only [Function.comp_apply, Real.toNNReal_coe] using! this
    have hU : Tendsto (fun j => ev (z (φ j))
        (Real.toNNReal (∑ i ∈ Finset.Iic (idx (φ j)), s (φ j) i))) atTop (𝓝 (ev a t)) :=
      (hev.tendsto (a, t)).comp (hlim1.prodMk_nhds (htime s hs))
    have hU' : Tendsto (fun j => ev (z' (φ j))
        (Real.toNNReal (∑ i ∈ Finset.Iic (idx (φ j)), s' (φ j) i))) atTop (𝓝 (ev a' t)) :=
      (hev.tendsto (a', t)).comp (hlim2.prodMk_nhds (htime s' hs'))
    have hd0 : Tendsto (fun j => dist (ev (z (φ j))
        (Real.toNNReal (∑ i ∈ Finset.Iic (idx (φ j)), s (φ j) i)))
        (ev (z' (φ j)) (Real.toNNReal (∑ i ∈ Finset.Iic (idx (φ j)), s' (φ j) i))))
        atTop (𝓝 0) := by
      refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine (hclose (φ j) (idx (φ j))).le.trans ?_
      have : (j : ℝ) ≤ φ j := by exact_mod_cast hφ.id_le j
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have := tendsto_nhds_unique (hU.dist hU') hd0
    exact dist_eq_zero.1 this
  rw [heq, dist_self] at hfar'
  exact absurd hfar' (not_le.2 hr)

/-! #### Weights -/
/-- Telescoping bound for the difference of two finite products. -/
theorem aux_prop_quenched_convergence_abs_prod_sub_prod_le :
    ∀ {k : ℕ} (α β : Fin k → ℝ) {M ε : ℝ}, 1 ≤ M → (∀ i, |α i| ≤ M) → (∀ i, |β i| ≤ M) →
      (∀ i, |α i - β i| ≤ ε) → |∏ i, α i - ∏ i, β i| ≤ k * ε * M ^ k
  | 0, α, β, M, ε, _, _, _, _ => by simp
  | k + 1, α, β, M, ε, hM, hα, hβ, hε => by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    have ih := aux_prop_quenched_convergence_abs_prod_sub_prod_le (fun i => α i.succ)
      (fun i => β i.succ) hM (fun i => hα _) (fun i => hβ _) (fun i => hε _)
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hε 0)
    have hA : |∏ i : Fin k, α i.succ| ≤ M ^ k := by
      rw [Finset.abs_prod]
      calc ∏ i : Fin k, |α i.succ| ≤ ∏ _i : Fin k, M :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hα _)
        _ = M ^ k := by simp
    have hMk : M ^ k ≤ M ^ (k + 1) := pow_le_pow_right₀ hM (Nat.le_succ k)
    have hM0 : 0 ≤ M := le_trans zero_le_one hM
    have e0 : α 0 * ∏ i : Fin k, α i.succ - β 0 * ∏ i : Fin k, β i.succ =
        (α 0 - β 0) * ∏ i : Fin k, α i.succ +
          β 0 * (∏ i : Fin k, α i.succ - ∏ i : Fin k, β i.succ) := by ring
    have e1 : M * (k * ε * M ^ k) = k * ε * M ^ (k + 1) := by ring
    have e2 : ε * M ^ k ≤ ε * M ^ (k + 1) := mul_le_mul_of_nonneg_left hMk hε0
    have e3 : ((k + 1 : ℕ) : ℝ) * ε * M ^ (k + 1) = k * ε * M ^ (k + 1) + ε * M ^ (k + 1) := by
      push_cast; ring
    rw [e0, e3]
    calc |(α 0 - β 0) * ∏ i : Fin k, α i.succ +
          β 0 * (∏ i : Fin k, α i.succ - ∏ i : Fin k, β i.succ)|
        ≤ |α 0 - β 0| * |∏ i : Fin k, α i.succ| +
            |β 0| * |∏ i : Fin k, α i.succ - ∏ i : Fin k, β i.succ| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ ε * M ^ k + M * (k * ε * M ^ k) := by
          gcongr
          · exact hε 0
          · exact hβ 0
      _ ≤ k * ε * M ^ (k + 1) + ε * M ^ (k + 1) := by rw [e1]; linarith

theorem aux_prop_quenched_convergence_posOrthant_eq (k : ℕ) :
    {s : Fin k → ℝ | ∀ i, 0 < s i} = Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ)) := by
  ext s; simp

/-- Integral of a product function over the positive orthant. -/
theorem aux_prop_quenched_convergence_integral_prod (k : ℕ) (g : ℝ → ℝ) :
    (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i}, ∏ i, g (s i)) = (∫ x in Ioi (0 : ℝ), g x) ^ k := by
  rw [aux_prop_quenched_convergence_posOrthant_eq, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun _ => g)]
  simp

theorem aux_prop_quenched_convergence_integrableOn_prod (k : ℕ) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ))) :
    IntegrableOn (fun s : Fin k → ℝ => ∏ i, g (s i)) {s : Fin k → ℝ | ∀ i, 0 < s i} := by
  rw [IntegrableOn, aux_prop_quenched_convergence_posOrthant_eq, volume_pi,
    Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (f := fun _ => g) (fun _ => hg)

theorem aux_prop_quenched_convergence_expSum_eq (k : ℕ) (s : Fin k → ℝ) :
    Real.exp (-(∑ i, s i)) = ∏ i, Real.exp (-(s i)) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]

/-- The unit-rate exponential weight on the positive orthant has integral one. -/
theorem aux_prop_quenched_convergence_expSum_integral (k : ℕ) :
    (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i}, Real.exp (-(∑ i, s i))) = 1 := by
  simp_rw [aux_prop_quenched_convergence_expSum_eq]
  rw [aux_prop_quenched_convergence_integral_prod k (fun x => Real.exp (-x)),
    integral_exp_neg_Ioi_zero, one_pow]

theorem aux_prop_quenched_convergence_expSum_integrableOn (k : ℕ) :
    IntegrableOn (fun s : Fin k → ℝ => Real.exp (-(∑ i, s i))) {s : Fin k → ℝ | ∀ i, 0 < s i} := by
  simp_rw [aux_prop_quenched_convergence_expSum_eq]
  exact aux_prop_quenched_convergence_integrableOn_prod k (fun x => Real.exp (-x))
    (integrableOn_exp_neg_Ioi 0)

/-- Discounted time weights.  A normalized bump `h` concentrated in the box
`|s i - Δ| < κ` is approximated, in weighted sup norm, by a finite linear combination of the
exponential weights `exp (-(∑ (n i + 1) s i))` of the determining functionals. -/
theorem aux_prop_quenched_convergence_weights (k : ℕ) {Δ κ : ℝ} (hκ : 0 < κ) (hκΔ : κ < Δ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ (h : (Fin k → ℝ) → ℝ) (D : ℕ) (c : (Fin k → ℕ) → ℝ),
      Continuous h ∧ (∀ s, 0 ≤ h s) ∧ (∀ s, h s ≠ 0 → ∀ i, |s i - Δ| < κ) ∧
      (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i}, h s) = 1 ∧
      IntegrableOn h {s : Fin k → ℝ | ∀ i, 0 < s i} ∧
      ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
        |(∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
            c n * Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i))) - h s| ≤
          τ * Real.exp (-(∑ i : Fin k, s i)) := by
  let b : ContDiffBump (Δ : ℝ) := ⟨κ / 2, κ, by linarith, by linarith⟩
  let h1 : ℝ → ℝ := b.normed volume
  have h1c : Continuous h1 := b.continuous_normed
  have h1nn : ∀ x, 0 ≤ h1 x := b.nonneg_normed
  have h1supp : ∀ x, h1 x ≠ 0 → |x - Δ| < κ := by
    intro x hx
    have hmem : x ∈ Function.support h1 := hx
    have hsupp : Function.support h1 = Metric.ball Δ κ := b.support_normed_eq
    rw [hsupp, Metric.mem_ball, Real.dist_eq] at hmem
    exact hmem
  have h1Ioi : ∫ x in Ioi (0 : ℝ), h1 x = 1 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact b.integral_normed
    · intro x hx
      by_contra hne
      have := h1supp x hne
      simp only [mem_Ioi, not_lt] at hx
      rw [abs_lt] at this
      linarith
  have h1int : IntegrableOn h1 (Ioi (0 : ℝ)) := b.integrable_normed.integrableOn
  -- the bump in the variable `x = exp (-s)`
  let q1 : ℝ → ℝ := fun x => h1 (-Real.log x) / x
  have hq1 : ∀ s : ℝ, Real.exp (-s) * q1 (Real.exp (-s)) = h1 s := by
    intro s
    simp only [q1, Real.log_exp, neg_neg]
    field_simp
  have hq1c : ContinuousOn q1 (Icc 0 1) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · subst hx0
      have hq0 : q1 0 = 0 := by simp [q1]
      have hev : q1 =ᶠ[𝓝[Icc 0 1] 0] fun _ => (0 : ℝ) := by
        have hI : Iio (Real.exp (-(Δ + κ))) ∈ 𝓝[Icc (0 : ℝ) 1] 0 :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (Real.exp_pos _))
        filter_upwards [hI, self_mem_nhdsWithin] with y hy hyI
        rcases eq_or_lt_of_le hyI.1 with hy0 | hy0
        · subst hy0; exact hq0
        · have hlog : Real.log y < -(Δ + κ) := (Real.log_lt_iff_lt_exp hy0).2 hy
          have hz : h1 (-Real.log y) = 0 := by
            by_contra hne
            have := h1supp _ hne
            rw [abs_lt] at this
            linarith
          simp [q1, hz]
      exact (continuousWithinAt_const.congr_of_eventuallyEq hev hq0)
    · have hcont : ContinuousAt q1 x :=
        ((h1c.continuousAt.comp (Real.continuousAt_log hx0.ne').neg).div continuousAt_id
          hx0.ne')
      exact hcont.continuousWithinAt
  obtain ⟨Q1, hQ1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hq1c
  set M : ℝ := |Q1| + 2 with hMdef
  have hM1 : 1 ≤ M := by have := abs_nonneg Q1; linarith
  have hMpos : 0 < (k : ℝ) * M ^ k + 1 := by positivity
  set ε : ℝ := min 1 (τ / ((k : ℝ) * M ^ k + 1)) with hεdef
  have hεpos : 0 < ε := lt_min one_pos (div_pos hτ hMpos)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hετ : (k : ℝ) * ε * M ^ k ≤ τ := by
    have h2 : ε ≤ τ / ((k : ℝ) * M ^ k + 1) := min_le_right _ _
    have h3 : ε * ((k : ℝ) * M ^ k + 1) ≤ τ := (le_div_iff₀ hMpos).1 h2
    have h4 : 0 ≤ ε := hεpos.le
    nlinarith
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 q1 hq1c ε hεpos
  set D : ℕ := p.natDegree + 1 with hD
  have key : ∀ x : ℝ, Real.exp (-x) * p.eval (Real.exp (-x)) =
      ∑ j ∈ Finset.range D, p.coeff j * Real.exp (-((j + 1 : ℝ) * x)) := by
    intro x
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  refine ⟨fun s => ∏ i, h1 (s i), D, fun n => ∏ i, p.coeff (n i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_finset_prod _ fun i _ => h1c.comp (continuous_apply i)
  · intro s
    exact Finset.prod_nonneg fun i _ => h1nn _
  · intro s hs i
    exact h1supp _ (Finset.prod_ne_zero_iff.1 hs i (Finset.mem_univ _))
  · rw [aux_prop_quenched_convergence_integral_prod k h1, h1Ioi, one_pow]
  · exact aux_prop_quenched_convergence_integrableOn_prod k h1 h1int
  · intro s hs
    have hexp : (∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
        (∏ i, p.coeff (n i)) * Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i))) =
        ∏ i, (Real.exp (-(s i)) * p.eval (Real.exp (-(s i)))) := by
      rw [Finset.prod_congr rfl (fun i _ => key (s i)), Finset.prod_univ_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_neg_distrib]
    rw [hexp]
    beta_reduce
    have hh : (∏ i, h1 (s i)) = ∏ i, (Real.exp (-(s i)) * q1 (Real.exp (-(s i)))) :=
      Finset.prod_congr rfl fun i _ => (hq1 (s i)).symm
    rw [hh, Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← mul_sub, abs_mul,
      aux_prop_quenched_convergence_expSum_eq]
    have hEnn : 0 ≤ ∏ i, Real.exp (-(s i)) := Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
    rw [abs_of_nonneg hEnn, mul_comm τ]
    refine mul_le_mul_of_nonneg_left ?_ hEnn
    have hmem : ∀ i, Real.exp (-(s i)) ∈ Icc (0 : ℝ) 1 := fun i =>
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith [hs i])⟩
    have hβ : ∀ i, |q1 (Real.exp (-(s i)))| ≤ M := by
      intro i
      have := hQ1 _ (hmem i)
      rw [Real.norm_eq_abs] at this
      have := le_abs_self Q1
      linarith
    have hαβ : ∀ i, |p.eval (Real.exp (-(s i))) - q1 (Real.exp (-(s i)))| ≤ ε :=
      fun i => (hp _ (hmem i)).le
    have hα : ∀ i, |p.eval (Real.exp (-(s i)))| ≤ M := by
      intro i
      have h1' := hαβ i
      have h2' := hQ1 _ (hmem i)
      rw [Real.norm_eq_abs] at h2'
      have h3' := le_abs_self Q1
      have : |p.eval (Real.exp (-(s i)))| ≤
          |p.eval (Real.exp (-(s i))) - q1 (Real.exp (-(s i)))| + |q1 (Real.exp (-(s i)))| := by
        have := abs_add_le (p.eval (Real.exp (-(s i))) - q1 (Real.exp (-(s i))))
          (q1 (Real.exp (-(s i))))
        simpa using this
      linarith
    exact (aux_prop_quenched_convergence_abs_prod_sub_prod_le _ _ hM1 hα hβ hαβ).trans hετ

/-! #### Paths -/
/-- A finite continuous partition of unity on a compact set, by bumps of small support. -/
theorem aux_prop_quenched_convergence_partition {E : Type*} [MetricSpace E] (Q : Set E)
    (hQ : IsCompact Q) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (p : ℕ) (β : Fin p → E →ᵇ ℝ), (∀ a y, 0 ≤ β a y) ∧ (∀ a y, β a y ≤ 1) ∧
      (∀ y, ∑ a, β a y ≤ 1) ∧ (∀ y ∈ Q, ∑ a, β a y = 1) ∧
      (∀ a y y', 0 < β a y → 0 < β a y' → dist y y' < θ) := by
  obtain ⟨t, _htQ, htfin, hcover⟩ := finite_cover_balls_of_compact hQ (half_pos hθ)
  haveI : Finite t := htfin.to_subtype
  obtain ⟨p, ⟨e⟩⟩ := Finite.exists_equiv_fin t
  let c : Fin p → E := fun a => (e.symm a : E)
  have hcover' : Q ⊆ ⋃ a, Metric.ball (c a) (θ / 2) := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcover hy)
    refine mem_iUnion.2 ⟨e ⟨x, hx⟩, ?_⟩
    simpa [c] using hyx
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate hQ.isClosed
    (fun a => Metric.ball (c a) (θ / 2)) (fun a => Metric.isOpen_ball) hcover'
  have hbd : ∀ a x y, dist (f a x) (f a y) ≤ 1 := by
    intro a x y
    rw [Real.dist_eq, abs_le]
    have := f.nonneg a x; have := f.nonneg a y
    have := f.le_one a x; have := f.le_one a y
    constructor <;> linarith
  let β : Fin p → E →ᵇ ℝ := fun a => BoundedContinuousFunction.mkOfBound (f a) 1 (hbd a)
  have hβ : ∀ a y, β a y = f a y := fun a y => rfl
  refine ⟨p, β, ?_, ?_, ?_, ?_, ?_⟩
  · intro a y; rw [hβ]; exact f.nonneg a y
  · intro a y; rw [hβ]; exact f.le_one a y
  · intro y
    have := f.sum_le_one y
    rw [finsum_eq_sum_of_fintype] at this
    simpa only [hβ] using this
  · intro y hy
    have := f.sum_eq_one hy
    rw [finsum_eq_sum_of_fintype] at this
    simpa only [hβ] using this
  · intro a y y' hy hy'
    rw [hβ] at hy hy'
    have h1 : y ∈ Metric.ball (c a) (θ / 2) :=
      hf a (subset_tsupport _ (Function.mem_support.2 hy.ne'))
    have h2 : y' ∈ Metric.ball (c a) (θ / 2) :=
      hf a (subset_tsupport _ (Function.mem_support.2 hy'.ne'))
    rw [Metric.mem_ball] at h1 h2
    calc dist y y' ≤ dist y (c a) + dist y' (c a) := dist_triangle_right _ _ _
      _ < θ / 2 + θ / 2 := add_lt_add h1 h2
      _ = θ := by ring



def aux_prop_quenched_convergence_psi {d : ℕ} (k : ℕ)
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ) (n : Fin k → ℕ)
    (path : DiffusionPath d) : ℝ :=
  ∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
    Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
      ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))

/-- A time-smoothed path functional with weight `w` and spatial profile `Φ`. -/
def aux_prop_quenched_convergence_smooth {d k : ℕ} (w : (Fin k → ℝ) → ℝ)
    (Φ : (Fin k → SpatialCoordinates d) → ℝ) (path : DiffusionPath d) : ℝ :=
  ∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
    w s * Φ (fun i => path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))

theorem aux_prop_quenched_convergence_psi_eq_smooth {d : ℕ} (k : ℕ)
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ) (n : Fin k → ℕ) :
    aux_prop_quenched_convergence_psi k f n =
      aux_prop_quenched_convergence_smooth
        (fun s => Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)))
        (fun y => ∏ i : Fin k, f i (y i)) := rfl

theorem aux_prop_quenched_convergence_posOrthant_measurable (k : ℕ) :
    MeasurableSet {s : Fin k → ℝ | ∀ i, 0 < s i} := by
  rw [aux_prop_quenched_convergence_posOrthant_eq]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi

theorem aux_prop_quenched_convergence_positions_continuous {d k : ℕ} :
    Continuous (fun q : DiffusionPath d × (Fin k → ℝ) =>
      (fun i : Fin k => q.1 (Real.toNNReal (∑ j ∈ Finset.Iic i, q.2 j)))) := by
  refine continuous_pi fun i => ?_
  have ht : Continuous (fun q : DiffusionPath d × (Fin k → ℝ) =>
      Real.toNNReal (∑ j ∈ Finset.Iic i, q.2 j)) :=
    continuous_real_toNNReal.comp
      (continuous_finset_sum _ fun j _ => (continuous_apply j).comp continuous_snd)
  exact continuous_eval.comp (continuous_fst.prodMk ht)

theorem aux_prop_quenched_convergence_smooth_measurable {d k : ℕ} (w : (Fin k → ℝ) → ℝ)
    (hw : Continuous w) (Φ : (Fin k → SpatialCoordinates d) → ℝ) (hΦ : Continuous Φ) :
    Measurable (aux_prop_quenched_convergence_smooth w Φ) := by
  have hF : Continuous (fun q : DiffusionPath d × (Fin k → ℝ) =>
      w q.2 * Φ (fun i => q.1 (Real.toNNReal (∑ j ∈ Finset.Iic i, q.2 j)))) :=
    (hw.comp continuous_snd).mul (hΦ.comp aux_prop_quenched_convergence_positions_continuous)
  exact (hF.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Fin k → ℝ)).restrict {s : Fin k → ℝ | ∀ i, 0 < s i})).measurable

/-- Integrability in time and the uniform bound of a smoothed functional whose weight is
dominated by the unit exponential. -/
theorem aux_prop_quenched_convergence_smooth_bound {d k : ℕ} (w : (Fin k → ℝ) → ℝ)
    (hw : Continuous w) (Φ : (Fin k → SpatialCoordinates d) → ℝ) (hΦ : Continuous Φ)
    {C B : ℝ} (hB : ∀ y, |Φ y| ≤ B)
    (hwC : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) → |w s| ≤ C * Real.exp (-(∑ i, s i)))
    (path : DiffusionPath d) :
    IntegrableOn (fun s : Fin k → ℝ =>
        w s * Φ (fun i => path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
      {s : Fin k → ℝ | ∀ i, 0 < s i} ∧
    |aux_prop_quenched_convergence_smooth w Φ path| ≤ C * B := by
  have hS := aux_prop_quenched_convergence_posOrthant_measurable k
  have hcont : Continuous (fun s : Fin k → ℝ =>
      w s * Φ (fun i => path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))) :=
    hw.mul (hΦ.comp (aux_prop_quenched_convergence_positions_continuous.comp
      (Continuous.prodMk continuous_const continuous_id)))
  have hdom : IntegrableOn (fun s : Fin k → ℝ => (C * B) * Real.exp (-(∑ i, s i)))
      {s : Fin k → ℝ | ∀ i, 0 < s i} :=
    (aux_prop_quenched_convergence_expSum_integrableOn k).const_mul (C * B)
  have hle : ∀ᵐ s ∂(volume.restrict {s : Fin k → ℝ | ∀ i, 0 < s i}),
      ‖w s * Φ (fun i => path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))‖ ≤
        (C * B) * Real.exp (-(∑ i, s i)) := by
    refine ae_restrict_of_forall_mem hS fun s hs => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hwC s hs
    have h2 := hB (fun i => path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))
    have hC0 : 0 ≤ C * Real.exp (-(∑ i, s i)) := le_trans (abs_nonneg _) h1
    calc |w s| * |Φ (fun i => path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))|
        ≤ (C * Real.exp (-(∑ i, s i))) * B :=
          mul_le_mul h1 h2 (abs_nonneg _) hC0
      _ = (C * B) * Real.exp (-(∑ i, s i)) := by ring
  refine ⟨hdom.mono' hcont.aestronglyMeasurable hle, ?_⟩
  have := norm_integral_le_of_norm_le hdom hle
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul, aux_prop_quenched_convergence_expSum_integral, mul_one]

theorem aux_prop_quenched_convergence_expRate_le {k : ℕ} (n : Fin k → ℕ) (s : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) :
    |Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i))| ≤ 1 * Real.exp (-(∑ i, s i)) := by
  rw [abs_of_pos (Real.exp_pos _), one_mul, Real.exp_le_exp, neg_le_neg_iff]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (1 : ℝ) ≤ (n i : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (n i); linarith
  nlinarith [hs i]

theorem aux_prop_quenched_convergence_expRate_continuous {k : ℕ} (n : Fin k → ℕ) :
    Continuous (fun s : Fin k → ℝ => Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i))) :=
  Real.continuous_exp.comp (continuous_finset_sum _ fun i _ =>
    continuous_const.mul (continuous_apply i)).neg

theorem aux_prop_quenched_convergence_prodProfile_continuous {d k : ℕ}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Continuous (fun y : Fin k → SpatialCoordinates d => ∏ i : Fin k, f i (y i)) :=
  continuous_finset_prod _ fun i _ => (f i).continuous.comp (continuous_apply i)

theorem aux_prop_quenched_convergence_prodProfile_bound {d k : ℕ}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hf0 : ∀ i y, 0 ≤ f i y) (hf1 : ∀ i y, f i y ≤ 1) (y : Fin k → SpatialCoordinates d) :
    |∏ i : Fin k, f i (y i)| ≤ 1 := by
  rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => hf0 i (y i))]
  exact Finset.prod_le_one₀ (fun i _ => hf0 i (y i)) (fun i _ => hf1 i (y i))

/-- Measurability, boundedness and integrability of the determining functionals built from
bumps with values in `[0, 1]`. -/
theorem aux_prop_quenched_convergence_psi_facts {d k : ℕ}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hf0 : ∀ i y, 0 ≤ f i y) (hf1 : ∀ i y, f i y ≤ 1) (n : Fin k → ℕ) :
    Measurable (aux_prop_quenched_convergence_psi k f n) ∧
      (∀ path, |aux_prop_quenched_convergence_psi k f n path| ≤ 1) ∧
      ∀ path : DiffusionPath d, IntegrableOn (fun s : Fin k → ℝ =>
        Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
          ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
        {s : Fin k → ℝ | ∀ i, 0 < s i} := by
  rw [aux_prop_quenched_convergence_psi_eq_smooth]
  have hb := fun path => aux_prop_quenched_convergence_smooth_bound (d := d) _
    (aux_prop_quenched_convergence_expRate_continuous n) _
    (aux_prop_quenched_convergence_prodProfile_continuous f)
    (aux_prop_quenched_convergence_prodProfile_bound f hf0 hf1)
    (aux_prop_quenched_convergence_expRate_le n) path
  refine ⟨aux_prop_quenched_convergence_smooth_measurable _
    (aux_prop_quenched_convergence_expRate_continuous n) _
    (aux_prop_quenched_convergence_prodProfile_continuous f), fun path => ?_,
    fun path => (hb path).1⟩
  simpa using (hb path).2

/-! #### Integration -/
/-- Integration of the pointwise sandwich used in the finite-test estimate. -/
theorem aux_prop_quenched_convergence_integration {X : Type*} [MeasurableSpace X]
    (μ μ' : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {A U Kc : Set X} (hA : MeasurableSet A) (hU : MeasurableSet U) (hKc : MeasurableSet Kc)
    (G Gt : X → ℝ) (hG : Measurable G) (hGt : Measurable Gt) {τ E : ℝ}
    (hG0 : ∀ z, 0 ≤ G z) (hG1 : ∀ z, G z ≤ 1)
    (h1 : ∀ z, A.indicator 1 z ≤ Kc.indicator 1 z + G z)
    (h2 : ∀ z, G z ≤ Gt z + τ) (h3 : ∀ z, Gt z ≤ G z + τ)
    (h4 : ∀ z, G z ≤ U.indicator 1 z + Kc.indicator 1 z)
    (h5 : ∫ z, Gt z ∂μ ≤ ∫ z, Gt z ∂μ' + E) :
    μ.real A ≤ μ'.real U + μ.real Kc + μ'.real Kc + 2 * τ + E := by
  have hGint : ∀ ν : Measure X, IsProbabilityMeasure ν → Integrable G ν := fun ν _ =>
    Integrable.of_bound hG.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 z)]; exact hG1 z)
  have hGtint : ∀ ν : Measure X, IsProbabilityMeasure ν → Integrable Gt ν := fun ν _ =>
    Integrable.of_bound hGt.aestronglyMeasurable (1 + |τ|)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_le]
        have := h2 z; have := h3 z; have := hG0 z; have := hG1 z
        have := le_abs_self τ; have := neg_abs_le τ
        constructor <;> linarith)
  have hind : ∀ (ν : Measure X) [IsProbabilityMeasure ν] (S : Set X), MeasurableSet S →
      Integrable (S.indicator (1 : X → ℝ)) ν := fun ν _ S hS =>
    (integrable_const (1 : ℝ)).indicator hS
  have hconst : ∀ (ν : Measure X) [IsProbabilityMeasure ν] (c : ℝ), ∫ _z, c ∂ν = c := by
    intro ν _ c; simp
  have s1 : μ.real A ≤ μ.real Kc + ∫ z, G z ∂μ := by
    rw [← integral_indicator_one hA, ← integral_indicator_one hKc,
      ← integral_add (hind μ Kc hKc) (hGint μ inferInstance)]
    exact integral_mono (hind μ A hA) ((hind μ Kc hKc).add (hGint μ inferInstance)) h1
  have s2 : ∫ z, G z ∂μ ≤ ∫ z, Gt z ∂μ + τ := by
    rw [← hconst μ τ, ← integral_add (hGtint μ inferInstance) (integrable_const τ)]
    exact integral_mono (hGint μ inferInstance) ((hGtint μ inferInstance).add
      (integrable_const τ)) h2
  have s4 : ∫ z, Gt z ∂μ' ≤ ∫ z, G z ∂μ' + τ := by
    rw [← hconst μ' τ, ← integral_add (hGint μ' inferInstance) (integrable_const τ)]
    exact integral_mono (hGtint μ' inferInstance) ((hGint μ' inferInstance).add
      (integrable_const τ)) h3
  have s5 : ∫ z, G z ∂μ' ≤ μ'.real U + μ'.real Kc := by
    rw [← integral_indicator_one hU, ← integral_indicator_one hKc,
      ← integral_add (hind μ' U hU) (hind μ' Kc hKc)]
    exact integral_mono (hGint μ' inferInstance) ((hind μ' U hU).add (hind μ' Kc hKc)) h4
  linarith

/-! #### Finite -/
theorem aux_prop_quenched_convergence_profile_sum_eq {d k p : ℕ}
    (β : Fin p → SpatialCoordinates d →ᵇ ℝ) (y : Fin k → SpatialCoordinates d) :
    ∑ a : Fin k → Fin p, ∏ i, β (a i) (y i) = ∏ i, ∑ b, β b (y i) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin p)))
    (fun i b => β b (y i))
  rw [h]
  simp only [Fintype.piFinset_univ]

theorem aux_prop_quenched_convergence_profile_bounds {d k p : ℕ}
    (β : Fin p → SpatialCoordinates d →ᵇ ℝ) (hβ0 : ∀ a y, 0 ≤ β a y)
    (hβs : ∀ y, ∑ a, β a y ≤ 1) (J : Finset (Fin k → Fin p))
    (y : Fin k → SpatialCoordinates d) :
    0 ≤ ∑ a ∈ J, ∏ i, β (a i) (y i) ∧ ∑ a ∈ J, ∏ i, β (a i) (y i) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun a _ => Finset.prod_nonneg fun i _ => hβ0 _ _
  · calc ∑ a ∈ J, ∏ i, β (a i) (y i) ≤ ∑ a : Fin k → Fin p, ∏ i, β (a i) (y i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
            (fun a _ _ => Finset.prod_nonneg fun i _ => hβ0 _ _)
      _ = ∏ i, ∑ b, β b (y i) := aux_prop_quenched_convergence_profile_sum_eq β y
      _ ≤ 1 := Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun b _ => hβ0 _ _)
          (fun i _ => hβs _)

theorem aux_prop_quenched_convergence_profile_one {d k p : ℕ}
    (β : Fin p → SpatialCoordinates d →ᵇ ℝ) (Q : Set (SpatialCoordinates d))
    (hβQ : ∀ y ∈ Q, ∑ a, β a y = 1) (J : Finset (Fin k → Fin p))
    (y : Fin k → SpatialCoordinates d) (hy : ∀ i, y i ∈ Q)
    (hJ : ∀ a ∉ J, ∏ i, β (a i) (y i) = 0) :
    ∑ a ∈ J, ∏ i, β (a i) (y i) = 1 := by
  rw [Finset.sum_subset (Finset.subset_univ J) (fun a _ ha => hJ a ha),
    aux_prop_quenched_convergence_profile_sum_eq]
  exact Finset.prod_eq_one fun i _ => hβQ _ (hy i)

theorem aux_prop_quenched_convergence_profile_continuous {d k p : ℕ}
    (β : Fin p → SpatialCoordinates d →ᵇ ℝ) (J : Finset (Fin k → Fin p)) :
    Continuous (fun y : Fin k → SpatialCoordinates d => ∑ a ∈ J, ∏ i, β (a i) (y i)) :=
  continuous_finset_sum _ fun a _ =>
    aux_prop_quenched_convergence_prodProfile_continuous (fun i => β (a i))

theorem aux_prop_quenched_convergence_prod_pos_factor {k : ℕ} (x : Fin k → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hpos : 0 < ∏ i, x i) (i : Fin k) : 0 < x i :=
  lt_of_le_of_ne (hx0 i) (Finset.prod_ne_zero_iff.1 hpos.ne' i (Finset.mem_univ i)).symm

/-- Bounds for the smoothed profile of a normalized nonnegative bump weight. -/
theorem aux_prop_quenched_convergence_G_bounds {d k : ℕ} (h : (Fin k → ℝ) → ℝ)
    (hh0 : ∀ s, 0 ≤ h s) (hh1 : (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i}, h s) = 1)
    (hhint : IntegrableOn h {s : Fin k → ℝ | ∀ i, 0 < s i})
    (Φ : (Fin k → SpatialCoordinates d) → ℝ) (hΦ0 : ∀ y, 0 ≤ Φ y) (hΦ1 : ∀ y, Φ y ≤ 1)
    (z : DiffusionPath d) :
    0 ≤ aux_prop_quenched_convergence_smooth h Φ z ∧
      aux_prop_quenched_convergence_smooth h Φ z ≤ 1 := by
  constructor
  · exact integral_nonneg fun s => mul_nonneg (hh0 s) (hΦ0 _)
  · rw [← hh1]
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => mul_nonneg (hh0 s) (hΦ0 _))
      hhint (Eventually.of_forall fun s => ?_)
    exact mul_le_of_le_one_right (hh0 s) (hΦ1 _)

theorem aux_prop_quenched_convergence_G_one {d k : ℕ} (h : (Fin k → ℝ) → ℝ)
    (hh1 : (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i}, h s) = 1)
    (Φ : (Fin k → SpatialCoordinates d) → ℝ) (z : DiffusionPath d)
    (hone : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) → h s ≠ 0 →
      Φ (fun i => z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))) = 1) :
    aux_prop_quenched_convergence_smooth h Φ z = 1 := by
  rw [← hh1]
  refine setIntegral_congr_fun (aux_prop_quenched_convergence_posOrthant_measurable k)
    fun s hs => ?_
  by_cases hs0 : h s = 0
  · simp [hs0]
  · rw [hone s hs hs0, mul_one]

theorem aux_prop_quenched_convergence_G_pos {d k p : ℕ} (h : (Fin k → ℝ) → ℝ)
    (β : Fin p → SpatialCoordinates d →ᵇ ℝ) (hβ0 : ∀ a y, 0 ≤ β a y)
    (J : Finset (Fin k → Fin p)) (z : DiffusionPath d)
    (hpos : 0 < aux_prop_quenched_convergence_smooth h
      (fun y : Fin k → SpatialCoordinates d => ∑ a ∈ J, ∏ i, β (a i) (y i)) z) :
    ∃ s : Fin k → ℝ, h s ≠ 0 ∧ ∃ a ∈ J,
      0 < ∏ i, β (a i) (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))) := by
  by_contra H
  push_neg at H
  have hzero : (fun s : Fin k → ℝ => h s *
      ∑ a ∈ J, ∏ i, β (a i) (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))) = fun _ => 0 := by
    funext s
    by_cases hs0 : h s = 0
    · simp [hs0]
    · have hsum : ∑ a ∈ J, ∏ i, β (a i) (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))) = 0 :=
        Finset.sum_eq_zero fun a ha =>
          le_antisymm (H s hs0 a ha) (Finset.prod_nonneg fun i _ => hβ0 _ _)
      rw [hsum, mul_zero]
  have : aux_prop_quenched_convergence_smooth h
      (fun y : Fin k → SpatialCoordinates d => ∑ a ∈ J, ∏ i, β (a i) (y i)) z = 0 := by
    unfold aux_prop_quenched_convergence_smooth
    rw [hzero]
    simp
  linarith

/-- The finite linear combination of determining functionals equals the smoothed profile
with the polynomial weight. -/
theorem aux_prop_quenched_convergence_Gt_eq {d k p : ℕ} (D : ℕ) (c : (Fin k → ℕ) → ℝ)
    (β : Fin p → SpatialCoordinates d →ᵇ ℝ) (hβ0 : ∀ a y, 0 ≤ β a y) (hβ1 : ∀ a y, β a y ≤ 1)
    (J : Finset (Fin k → Fin p)) (z : DiffusionPath d) :
    ∑ a ∈ J, ∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
        c n * aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z =
      aux_prop_quenched_convergence_smooth
        (fun s => ∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
          c n * Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)))
        (fun y : Fin k → SpatialCoordinates d => ∑ a ∈ J, ∏ i, β (a i) (y i)) z := by
  have hint : ∀ (a : Fin k → Fin p) (n : Fin k → ℕ), IntegrableOn (fun s : Fin k → ℝ =>
      Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
        ∏ i : Fin k, β (a i) (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
      {s : Fin k → ℝ | ∀ i, 0 < s i} := fun a n =>
    (aux_prop_quenched_convergence_psi_facts (fun i => β (a i)) (fun i => hβ0 _)
      (fun i => hβ1 _) n).2.2 z
  unfold aux_prop_quenched_convergence_smooth aux_prop_quenched_convergence_psi
  have hexpand : ∀ s : Fin k → ℝ,
      (∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
          c n * Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i))) *
        ∑ a ∈ J, ∏ i, β (a i) (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))) =
      ∑ a ∈ J, ∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
        c n * (Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
          ∏ i : Fin k, β (a i) (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))) := by
    intro s
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  simp_rw [hexpand]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun n _ =>
    (hint a n).const_mul (c n))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ (fun n _ => (hint a n).const_mul (c n))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul]

/-- Closeness of the polynomial-weight and bump-weight smoothed profiles. -/
theorem aux_prop_quenched_convergence_Gt_close {d k : ℕ} (h w : (Fin k → ℝ) → ℝ)
    (hhc : Continuous h) (hh0 : ∀ s, 0 ≤ h s)
    (hhint : IntegrableOn h {s : Fin k → ℝ | ∀ i, 0 < s i}) (hwc : Continuous w) {τ : ℝ}
    (happrox : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) → |w s - h s| ≤ τ * Real.exp (-(∑ i, s i)))
    (Φ : (Fin k → SpatialCoordinates d) → ℝ) (hΦc : Continuous Φ) (hΦ0 : ∀ y, 0 ≤ Φ y)
    (hΦ1 : ∀ y, Φ y ≤ 1) (z : DiffusionPath d) :
    |aux_prop_quenched_convergence_smooth w Φ z - aux_prop_quenched_convergence_smooth h Φ z|
      ≤ τ := by
  have hΦabs : ∀ y, |Φ y| ≤ 1 := fun y => by rw [abs_of_nonneg (hΦ0 y)]; exact hΦ1 y
  obtain ⟨hint1, hbd⟩ := aux_prop_quenched_convergence_smooth_bound (fun s => w s - h s)
    (hwc.sub hhc) Φ hΦc hΦabs happrox z
  have hcont : Continuous (fun s : Fin k → ℝ =>
      h s * Φ (fun i => z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))) :=
    hhc.mul (hΦc.comp (aux_prop_quenched_convergence_positions_continuous.comp
      (Continuous.prodMk continuous_const continuous_id)))
  have hint2 : IntegrableOn (fun s : Fin k → ℝ =>
      h s * Φ (fun i => z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
      {s : Fin k → ℝ | ∀ i, 0 < s i} := by
    refine hhint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh0 s)]
    exact mul_le_of_le_one_right (hh0 s) (hΦabs _)
  have heq : aux_prop_quenched_convergence_smooth w Φ z =
      aux_prop_quenched_convergence_smooth (fun s => w s - h s) Φ z +
        aux_prop_quenched_convergence_smooth h Φ z := by
    unfold aux_prop_quenched_convergence_smooth
    rw [← integral_add hint1 hint2]
    congr 1
    funext s
    ring
  rw [heq, add_sub_cancel_right]
  simpa using hbd

/-- Finite-sum bookkeeping for the test differences. -/
theorem aux_prop_quenched_convergence_test_sum {ι ν : Type*} [Fintype ι]
    (J : Finset ι) (N : Finset ν) (c : ν → ℝ) (x y : ι → ν → ℝ) {ϱ : ℝ}
    (hxy : ∀ a, ∀ n ∈ N, |x a n - y a n| ≤ ϱ) :
    ∑ a ∈ J, ∑ n ∈ N, c n * x a n ≤
      ∑ a ∈ J, ∑ n ∈ N, c n * y a n + ((Fintype.card ι : ℝ) * ∑ n ∈ N, |c n|) * ϱ := by
  have hϱ : ∀ (a : ι) (n : ν), n ∈ N → c n * x a n ≤ c n * y a n + |c n| * ϱ := by
    intro a n hn
    have h1 : c n * (x a n - y a n) ≤ |c n * (x a n - y a n)| := le_abs_self _
    rw [abs_mul] at h1
    have h2 : |c n| * |x a n - y a n| ≤ |c n| * ϱ :=
      mul_le_mul_of_nonneg_left (hxy a n hn) (abs_nonneg _)
    nlinarith
  have hϱ0 : ∀ (a : ι) (n : ν), n ∈ N → 0 ≤ |c n| * ϱ := by
    intro a n hn
    exact mul_nonneg (abs_nonneg _) (le_trans (abs_nonneg _) (hxy a n hn))
  calc ∑ a ∈ J, ∑ n ∈ N, c n * x a n
      ≤ ∑ a ∈ J, ∑ n ∈ N, (c n * y a n + |c n| * ϱ) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun n hn => hϱ a n hn
    _ = ∑ a ∈ J, ∑ n ∈ N, c n * y a n + ∑ a ∈ J, ∑ n ∈ N, |c n| * ϱ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
    _ ≤ ∑ a ∈ J, ∑ n ∈ N, c n * y a n + ∑ a : ι, ∑ n ∈ N, |c n| * ϱ := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
          (fun (a : ι) _ _ => Finset.sum_nonneg fun n hn => hϱ0 a n hn)
        linarith
    _ = ∑ a ∈ J, ∑ n ∈ N, c n * y a n + ((Fintype.card ι : ℝ) * ∑ n ∈ N, |c n|) * ϱ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul]
        ring

/-! #### FT -/
/-- The metric-free sandwich estimate behind the finite-test extraction: for a Borel set `A`,
the probability of `A` under `μ` is controlled by the probability under `μ'` of any set `U`
that contains every path of `K` which is grid-close to a path of `A ∩ K`, up to the masses off
`K`, the time-weight error and the finitely many test differences. -/
theorem aux_prop_quenched_convergence_core {d k p D : ℕ} (K : Set (DiffusionPath d))
    (hKm : MeasurableSet K) (Q : Set (SpatialCoordinates d)) {Δ κ θ τ : ℝ}
    (hQmem : ∀ z ∈ K, ∀ s : Fin k → ℝ, (∀ i, |s i - Δ| < κ) →
      ∀ i, z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)) ∈ Q)
    (β : Fin p → SpatialCoordinates d →ᵇ ℝ) (hβ0 : ∀ a y, 0 ≤ β a y)
    (hβ1 : ∀ a y, β a y ≤ 1) (hβs : ∀ y, ∑ a, β a y ≤ 1) (hβQ : ∀ y ∈ Q, ∑ a, β a y = 1)
    (hβsep : ∀ a y y', 0 < β a y → 0 < β a y' → dist y y' < θ)
    (h : (Fin k → ℝ) → ℝ) (c : (Fin k → ℕ) → ℝ) (hhc : Continuous h) (hh0 : ∀ s, 0 ≤ h s)
    (hhbox : ∀ s, h s ≠ 0 → ∀ i, |s i - Δ| < κ)
    (hh1 : (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i}, h s) = 1)
    (hhint : IntegrableOn h {s : Fin k → ℝ | ∀ i, 0 < s i})
    (happrox : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      |(∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
          c n * Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i))) - h s| ≤
        τ * Real.exp (-(∑ i : Fin k, s i)))
    (μ μ' : Measure (DiffusionPath d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {ϱ : ℝ}
    (htest : ∀ a : Fin k → Fin p, ∀ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
      |(∫ z, aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z ∂μ) -
        ∫ z, aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z ∂μ'| ≤ ϱ)
    (A U : Set (DiffusionPath d)) (hA : MeasurableSet A) (hU : MeasurableSet U)
    (hAU : ∀ z ∈ K, ∀ z₀ ∈ A, z₀ ∈ K → ∀ s s' : Fin k → ℝ, (∀ i, |s i - Δ| < κ) →
      (∀ i, |s' i - Δ| < κ) →
      (∀ i, dist (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))
        (z₀ (Real.toNNReal (∑ j ∈ Finset.Iic i, s' j))) < θ) → z ∈ U) :
    μ.real A ≤ μ'.real U + μ.real Kᶜ + μ'.real Kᶜ + 2 * τ +
      ((Fintype.card (Fin k → Fin p) : ℝ) *
        ∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D), |c n|) * ϱ := by
  classical
  let N := Fintype.piFinset (fun _ : Fin k => Finset.range D)
  let J : Finset (Fin k → Fin p) := Finset.univ.filter (fun a => ∃ z₀ ∈ A, z₀ ∈ K ∧
    ∃ s : Fin k → ℝ, (∀ i, |s i - Δ| < κ) ∧
      0 < ∏ i, β (a i) (z₀ (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
  let Φ : (Fin k → SpatialCoordinates d) → ℝ := fun y => ∑ a ∈ J, ∏ i, β (a i) (y i)
  let w : (Fin k → ℝ) → ℝ := fun s =>
    ∑ n ∈ N, c n * Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i))
  let G : DiffusionPath d → ℝ := aux_prop_quenched_convergence_smooth h Φ
  let Gt : DiffusionPath d → ℝ := fun z =>
    ∑ a ∈ J, ∑ n ∈ N, c n * aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z
  have hΦb := aux_prop_quenched_convergence_profile_bounds β hβ0 hβs J
  have hΦc : Continuous Φ := aux_prop_quenched_convergence_profile_continuous β J
  have hGb : ∀ z, 0 ≤ G z ∧ G z ≤ 1 := fun z =>
    aux_prop_quenched_convergence_G_bounds h hh0 hh1 hhint Φ (fun y => (hΦb y).1)
      (fun y => (hΦb y).2) z
  have hwc : Continuous w := continuous_finset_sum _ fun n _ =>
    continuous_const.mul (aux_prop_quenched_convergence_expRate_continuous n)
  have hclose : ∀ z, |Gt z - G z| ≤ τ := by
    intro z
    have hGt_eq : Gt z = aux_prop_quenched_convergence_smooth w Φ z :=
      aux_prop_quenched_convergence_Gt_eq D c β hβ0 hβ1 J z
    rw [hGt_eq]
    exact aux_prop_quenched_convergence_Gt_close h w hhc hh0 hhint hwc happrox Φ hΦc
      (fun y => (hΦb y).1) (fun y => (hΦb y).2) z
  have hpsi := fun (a : Fin k → Fin p) (n : Fin k → ℕ) =>
    aux_prop_quenched_convergence_psi_facts (fun i => β (a i)) (fun i => hβ0 _)
      (fun i => hβ1 _) n
  have hGm : Measurable G := aux_prop_quenched_convergence_smooth_measurable h hhc Φ hΦc
  have hGtm : Measurable Gt := Finset.measurable_sum _ fun a _ =>
    Finset.measurable_sum _ fun n _ => (hpsi a n).1.const_mul (c n)
  have hind0 : ∀ (S : Set (DiffusionPath d)) z, 0 ≤ S.indicator (1 : DiffusionPath d → ℝ) z :=
    fun S z => indicator_nonneg (fun _ _ => zero_le_one) z
  have h1 : ∀ z, A.indicator 1 z ≤ Kᶜ.indicator 1 z + G z := by
    intro z
    by_cases hzA : z ∈ A
    · by_cases hzK : z ∈ K
      · have hG1 : G z = 1 := by
          refine aux_prop_quenched_convergence_G_one h hh1 Φ z fun s _ hs0 => ?_
          refine aux_prop_quenched_convergence_profile_one β Q hβQ J _
            (fun i => hQmem z hzK s (hhbox s hs0) i) fun a haJ => ?_
          by_contra hne
          have hpos : 0 < ∏ i, β (a i) (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))) :=
            lt_of_le_of_ne (Finset.prod_nonneg fun i _ => hβ0 _ _) (Ne.symm hne)
          exact haJ (Finset.mem_filter.2
            ⟨Finset.mem_univ _, z, hzA, hzK, s, hhbox s hs0, hpos⟩)
        rw [indicator_of_mem hzA, indicator_of_notMem (show z ∉ Kᶜ from fun h' => h' hzK), hG1]
        simp
      · rw [indicator_of_mem hzA, indicator_of_mem (show z ∈ Kᶜ from hzK)]
        have := (hGb z).1
        simp only [Pi.one_apply]
        linarith
    · rw [indicator_of_notMem hzA]
      have := (hGb z).1
      have := hind0 Kᶜ z
      linarith
  have h4 : ∀ z, G z ≤ U.indicator 1 z + Kᶜ.indicator 1 z := by
    intro z
    have hU0 := hind0 U z
    have hK0 := hind0 Kᶜ z
    by_cases hzK : z ∈ K
    · by_cases hGz : G z ≤ 0
      · linarith
      · push_neg at hGz
        obtain ⟨s, hs0, a, haJ, hpos⟩ := aux_prop_quenched_convergence_G_pos h β hβ0 J z hGz
        obtain ⟨-, z₀, hz₀A, hz₀K, s', hs'box, hpos'⟩ := Finset.mem_filter.1 haJ
        have hzU : z ∈ U := hAU z hzK z₀ hz₀A hz₀K s s' (hhbox s hs0) hs'box fun i =>
          hβsep (a i) _ _
            (aux_prop_quenched_convergence_prod_pos_factor _ (fun i => hβ0 _ _) hpos i)
            (aux_prop_quenched_convergence_prod_pos_factor _ (fun i => hβ0 _ _) hpos' i)
        rw [indicator_of_mem hzU]
        have := (hGb z).2
        simp only [Pi.one_apply]
        linarith
    · rw [indicator_of_mem (show z ∈ Kᶜ from hzK)]
      have := (hGb z).2
      simp only [Pi.one_apply]
      linarith
  have hint : ∀ (ν : Measure (DiffusionPath d)) [IsProbabilityMeasure ν]
      (a : Fin k → Fin p) (n : Fin k → ℕ),
      Integrable (aux_prop_quenched_convergence_psi k (fun i => β (a i)) n) ν :=
    fun ν _ a n => Integrable.of_bound (hpsi a n).1.aestronglyMeasurable 1
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hpsi a n).2.1 z)
  have hIGt : ∀ (ν : Measure (DiffusionPath d)) [IsProbabilityMeasure ν],
      ∫ z, Gt z ∂ν = ∑ a ∈ J, ∑ n ∈ N,
        c n * ∫ z, aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z ∂ν := by
    intro ν _
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun n _ =>
      (hint ν a n).const_mul (c n))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ (fun n _ => (hint ν a n).const_mul (c n))]
    exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _
  have h5 : ∫ z, Gt z ∂μ ≤ ∫ z, Gt z ∂μ' +
      ((Fintype.card (Fin k → Fin p) : ℝ) * ∑ n ∈ N, |c n|) * ϱ := by
    rw [hIGt μ, hIGt μ']
    exact aux_prop_quenched_convergence_test_sum J N c
      (fun a n => ∫ z, aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z ∂μ)
      (fun a n => ∫ z, aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z ∂μ') htest
  exact aux_prop_quenched_convergence_integration μ μ' hA hU hKm.compl G Gt hGm hGtm
    (fun z => (hGb z).1) (fun z => (hGb z).2) h1
    (fun z => by have := hclose z; rw [abs_le] at this; linarith)
    (fun z => by have := hclose z; rw [abs_le] at this; linarith) h4 h5

theorem aux_prop_quenched_convergence_positions_mem {d k : ℕ} (K : Set (DiffusionPath d))
    {Δ κ : ℝ} (z : DiffusionPath d) (hz : z ∈ K) (s : Fin k → ℝ)
    (hs : ∀ i, |s i - Δ| < κ) (hκΔ : κ < Δ) (i : Fin k) :
    z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)) ∈
      (fun q : DiffusionPath d × ℝ≥0 => q.1 q.2) ''
        (K ×ˢ Icc 0 (Real.toNNReal (k * (Δ + κ)))) := by
  refine ⟨(z, Real.toNNReal (∑ j ∈ Finset.Iic i, s j)), ⟨hz, zero_le, ?_⟩, rfl⟩
  apply Real.toNNReal_le_toNNReal
  have hpos : ∀ j, 0 ≤ s j := fun j => by
    have := hs j; rw [abs_lt] at this; linarith
  have hle : ∀ j, s j ≤ Δ + κ := fun j => by
    have := hs j; rw [abs_lt] at this; linarith
  calc ∑ j ∈ Finset.Iic i, s j ≤ ∑ j, s j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hpos j)
    _ ≤ ∑ _j : Fin k, (Δ + κ) := Finset.sum_le_sum fun j _ => hle j
    _ = k * (Δ + κ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Finite-test extraction.**  On laws charging a compact path set `K` up to mass `δ`,
finitely many determining functionals control the Lévy–Prokhorov distance: agreement within
`ϱ` on the tests forces distance at most `η + 2δ + C ϱ`, where the tests and `C` depend only
on `K` and `η`. -/
theorem aux_prop_quenched_convergence_finite_tests {d : ℕ} (K : Set (DiffusionPath d))
    (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ (k p D : ℕ) (β : Fin p → SpatialCoordinates d →ᵇ ℝ) (c : (Fin k → ℕ) → ℝ),
      (∀ a y, 0 ≤ β a y) ∧ (∀ a y, β a y ≤ 1) ∧
      ∀ (P P' : ProbabilityMeasure (DiffusionPath d)) (δ ϱ : ℝ), 0 ≤ δ → 0 ≤ ϱ →
        (P : Measure (DiffusionPath d)) Kᶜ ≤ ENNReal.ofReal δ →
        (P' : Measure (DiffusionPath d)) Kᶜ ≤ ENNReal.ofReal δ →
        (∀ a : Fin k → Fin p, ∀ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
          |(∫ z, aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z
              ∂(P : Measure (DiffusionPath d))) -
            ∫ z, aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z
              ∂(P' : Measure (DiffusionPath d))| ≤ ϱ) →
        pathLevyProkhorovDist P P' ≤ η + 2 * δ +
          ((Fintype.card (Fin k → Fin p) : ℝ) *
            ∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D), |c n|) * ϱ := by
  classical
  letI : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  obtain ⟨k, Δ, κ, θ, _hΔ, hκ, hκΔ, hθ, hgrid⟩ :=
    aux_prop_quenched_convergence_grid (X := DiffusionPath d) (E := SpatialCoordinates d)
      (fun z t => z t) continuous_eval (fun z z' h => ContinuousMap.ext h) K hK (half_pos hη)
  have hQc : IsCompact ((fun q : DiffusionPath d × ℝ≥0 => q.1 q.2) ''
      (K ×ˢ Icc 0 (Real.toNNReal (k * (Δ + κ))))) :=
    (hK.prod isCompact_Icc).image continuous_eval
  obtain ⟨p, β, hβ0, hβ1, hβs, hβQ, hβsep⟩ := aux_prop_quenched_convergence_partition _ hQc hθ
  obtain ⟨h, D, c, hhc, hh0, hhbox, hh1, hhint, happrox⟩ :=
    aux_prop_quenched_convergence_weights k hκ hκΔ (τ := η / 4) (by positivity)
  refine ⟨k, p, D, β, c, hβ0, hβ1, ?_⟩
  intro P P' δ ϱ hδ hϱ hPK hP'K htest
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = (Fintype.card (Fin k → Fin p) : ℝ) *
      ∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D), |c n| := ⟨_, rfl⟩
  rw [← hCc]
  have hCc0 : 0 ≤ Cc := by
    rw [hCc]; exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _)
  show levyProkhorovDist (P : Measure (DiffusionPath d)) (P' : Measure (DiffusionPath d)) ≤ _
  apply levyProkhorovDist_le_of_forall_le _ _ (by positivity)
  intro ε A hε hA
  have hcore := aux_prop_quenched_convergence_core K hK.isClosed.measurableSet _
    (fun z hz s hs i => aux_prop_quenched_convergence_positions_mem K z hz s hs hκΔ i)
    β hβ0 hβ1 hβs hβQ hβsep h c hhc hh0 hhbox hh1 hhint happrox
    (P : Measure (DiffusionPath d)) (P' : Measure (DiffusionPath d)) htest
    A (Metric.thickening (η / 2) A) hA Metric.isOpen_thickening.measurableSet
    (fun z hz z₀ hz₀A hz₀K s s' hs hs' hd =>
      Metric.mem_thickening_iff.2 ⟨z₀, hz₀A, hgrid z hz z₀ hz₀K s s' hs hs' hd⟩)
  rw [← hCc] at hcore
  have hPK' : (P : Measure (DiffusionPath d)).real Kᶜ ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ hPK
  have hP'K' : (P' : Measure (DiffusionPath d)).real Kᶜ ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ hP'K
  have hreal : (P : Measure (DiffusionPath d)).real A ≤
      (P' : Measure (DiffusionPath d)).real (Metric.thickening (η / 2) A) +
        (2 * δ + η / 2 + Cc * ϱ) := by linarith
  have hCϱ : 0 ≤ Cc * ϱ := mul_nonneg hCc0 hϱ
  have hε' : η / 2 ≤ ε := by linarith
  have hX : 0 ≤ 2 * δ + η / 2 + Cc * ϱ := by positivity
  calc (P : Measure (DiffusionPath d)) A
      = ENNReal.ofReal ((P : Measure (DiffusionPath d)).real A) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal ((P' : Measure (DiffusionPath d)).real (Metric.thickening (η / 2) A) +
          (2 * δ + η / 2 + Cc * ϱ)) := ENNReal.ofReal_le_ofReal hreal
    _ = (P' : Measure (DiffusionPath d)) (Metric.thickening (η / 2) A) +
          ENNReal.ofReal (2 * δ + η / 2 + Cc * ϱ) := by
        rw [ENNReal.ofReal_add measureReal_nonneg hX, ofReal_measureReal]
    _ ≤ (P' : Measure (DiffusionPath d)) (Metric.thickening ε A) + ENNReal.ofReal ε :=
        add_le_add (measure_mono (Metric.thickening_mono hε' A))
          (ENNReal.ofReal_le_ofReal (by linarith))

/-! #### Main -/
/-- Markov's inequality for the uniform-in-start tightness event of one kernel. -/
theorem aux_prop_quenched_convergence_tight_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsProbabilityMeasure μ]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (B : Set (SpatialCoordinates d)) (hB : IsCompact B) (Kset : Set (DiffusionPath d))
    (hKset : IsCompact Kset) {δ r : ℝ} (hδ : 0 < δ)
    (hint : (∫⁻ omega, ⨆ x ∈ B, (K (omega, x)) Ksetᶜ ∂μ) ≤ ENNReal.ofReal (r * δ)) :
    μ {omega | ∃ x ∈ B, ENNReal.ofReal δ < K (omega, x) Ksetᶜ} ≤ ENNReal.ofReal r := by
  haveI : PolishSpace (BilateralField d) := {}
  have hF : Measurable (fun q : BilateralField d × SpatialCoordinates d => K q Ksetᶜ) :=
    K.measurable_coe hKset.isClosed.measurableSet.compl
  have hM := aux_prop_quenched_convergence_markov_sup μ
    (fun q : BilateralField d × SpatialCoordinates d => K q Ksetᶜ) hF B
    hB.isClosed.measurableSet (ENNReal.ofReal δ)
  have h2 : ENNReal.ofReal δ * μ {omega | ∃ x ∈ B, ENNReal.ofReal δ < K (omega, x) Ksetᶜ} ≤
      ENNReal.ofReal δ * ENNReal.ofReal r := by
    refine hM.trans (hint.trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_mul hδ.le, mul_comm]
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top).1 h2

theorem aux_prop_quenched_convergence_arith_tests {Cc eps : ℝ} (hCc : 0 ≤ Cc)
    (heps : 0 < eps) : Cc * (eps / (8 * (Cc + 1))) ≤ eps / 8 := by
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  have : 0 ≤ eps * 8 := by positivity
  nlinarith

theorem aux_prop_quenched_convergence_arith_sum (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ENNReal.ofReal (rho / 4) + ENNReal.ofReal (rho / 4) +
      (m : ℝ≥0∞) * ENNReal.ofReal (rho / (4 * ((m : ℝ) + 1))) ≤ ENNReal.ofReal rho := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul hm,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h : (m : ℝ) * (rho / (4 * ((m : ℝ) + 1))) ≤ rho / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- The quenched-convergence argument on a general probability law of the fields. -/
theorem aux_prop_quenched_convergence_main {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsProbabilityMeasure μ]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hcauchy : ∀ (k : ℕ) (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (n : Fin k → ℕ) (B : Set (SpatialCoordinates d)), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
        μ {omega : BilateralField d | ∃ x ∈ B, eps ≤
              |(∫ path, aux_prop_quenched_convergence_psi k f n path ∂(KN N (omega, x))) -
                (∫ path, aux_prop_quenched_convergence_psi k f n path ∂(KN N' (omega, x)))|} ≤
          ENNReal.ofReal rho)
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
          ∀ N : ℕ, (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ ∂μ) ≤ ENNReal.ofReal epsilon)
    (B : Set (SpatialCoordinates d)) (hB : IsCompact B) (eps : ℝ) (heps : 0 < eps) (rho : ℝ)
    (hrho : 0 < rho) :
    ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
      μ {omega : BilateralField d | ∃ x ∈ B, eps ≤
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
            (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
        ENNReal.ofReal rho := by
  classical
  obtain ⟨Kset, hKset, hKint⟩ := htight B hB (rho / 4 * (eps / 8)) (by positivity)
  obtain ⟨k, p, D, β, c, _hβ0, _hβ1, hFT⟩ :=
    aux_prop_quenched_convergence_finite_tests Kset hKset (η := eps / 4) (by positivity)
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = (Fintype.card (Fin k → Fin p) : ℝ) *
      ∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D), |c n| := ⟨_, rfl⟩
  have hCc0 : 0 ≤ Cc := by
    rw [hCc]; exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _)
  obtain ⟨ϱ, hϱ⟩ : ∃ ϱ : ℝ, ϱ = eps / (8 * (Cc + 1)) := ⟨_, rfl⟩
  have hϱpos : 0 < ϱ := by rw [hϱ]; positivity
  have hCϱ : Cc * ϱ ≤ eps / 8 := by
    rw [hϱ]; exact aux_prop_quenched_convergence_arith_tests hCc0 heps
  let T : Finset ((Fin k → Fin p) × (Fin k → ℕ)) :=
    Finset.univ ×ˢ Fintype.piFinset (fun _ : Fin k => Finset.range D)
  have hc := fun (q : (Fin k → Fin p) × (Fin k → ℕ)) =>
    hcauchy k (fun i => β (q.1 i)) q.2 B hB ϱ hϱpos
      (rho / (4 * ((T.card : ℝ) + 1))) (by positivity)
  choose N0f hN0f using hc
  refine ⟨T.sup N0f, fun N N' hN hN' => ?_⟩
  let tight : ℕ → Set (BilateralField d) := fun N =>
    {omega | ∃ x ∈ B, ENNReal.ofReal (eps / 8) < KN N (omega, x) Ksetᶜ}
  let C : (Fin k → Fin p) × (Fin k → ℕ) → Set (BilateralField d) := fun q =>
    {omega | ∃ x ∈ B, ϱ ≤
      |(∫ path, aux_prop_quenched_convergence_psi k (fun i => β (q.1 i)) q.2 path
          ∂(KN N (omega, x))) -
        (∫ path, aux_prop_quenched_convergence_psi k (fun i => β (q.1 i)) q.2 path
          ∂(KN N' (omega, x)))|}
  have hsub : {omega : BilateralField d | ∃ x ∈ B, eps ≤
      pathLevyProkhorovDist
        (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
        (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ⊆
      tight N ∪ tight N' ∪ ⋃ q ∈ T, C q := by
    rintro omega ⟨x, hx, hd⟩
    by_contra hnot
    have h1 : omega ∉ tight N := fun h => hnot (Or.inl (Or.inl h))
    have h2 : omega ∉ tight N' := fun h => hnot (Or.inl (Or.inr h))
    have h3 : ∀ q ∈ T, omega ∉ C q := fun q hq h =>
      hnot (Or.inr (Set.mem_biUnion hq h))
    have hK1 : KN N (omega, x) Ksetᶜ ≤ ENNReal.ofReal (eps / 8) :=
      not_lt.1 fun h => h1 ⟨x, hx, h⟩
    have hK2 : KN N' (omega, x) Ksetᶜ ≤ ENNReal.ofReal (eps / 8) :=
      not_lt.1 fun h => h2 ⟨x, hx, h⟩
    have htests : ∀ a : Fin k → Fin p, ∀ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.range D),
        |(∫ z, aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z
            ∂((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
              ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))) -
          ∫ z, aux_prop_quenched_convergence_psi k (fun i => β (a i)) n z
            ∂((jointPathProbabilityMeasure (KN N') (hKN N') omega x :
              ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))| ≤ ϱ := by
      intro a n hn
      have hq : (a, n) ∈ T := Finset.mem_product.2 ⟨Finset.mem_univ _, hn⟩
      exact (not_le.1 fun h => h3 (a, n) hq ⟨x, hx, h⟩).le
    have hbound := hFT (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
      (jointPathProbabilityMeasure (KN N') (hKN N') omega x) (eps / 8) ϱ (by positivity)
      hϱpos.le hK1 hK2 htests
    rw [← hCc] at hbound
    linarith
  have htightN : ∀ M : ℕ, μ (tight M) ≤ ENNReal.ofReal (rho / 4) := fun M =>
    aux_prop_quenched_convergence_tight_event μ (KN M) B hB Kset hKset
      (by positivity : (0 : ℝ) < eps / 8) (hKint M)
  have hC : ∀ q ∈ T, μ (C q) ≤ ENNReal.ofReal (rho / (4 * ((T.card : ℝ) + 1))) :=
    fun q hq => hN0f q N N' ((Finset.le_sup hq).trans hN) ((Finset.le_sup hq).trans hN')
  calc μ {omega : BilateralField d | ∃ x ∈ B, eps ≤
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure (KN N') (hKN N') omega x)}
      ≤ μ (tight N ∪ tight N' ∪ ⋃ q ∈ T, C q) := measure_mono hsub
    _ ≤ μ (tight N) + μ (tight N') + ∑ q ∈ T, μ (C q) :=
        (measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal (rho / 4) + ENNReal.ofReal (rho / 4) +
          ∑ _q ∈ T, ENNReal.ofReal (rho / (4 * ((T.card : ℝ) + 1))) :=
        add_le_add (add_le_add (htightN N) (htightN N')) (Finset.sum_le_sum hC)
    _ = ENNReal.ofReal (rho / 4) + ENNReal.ofReal (rho / 4) +
          (T.card : ℝ≥0∞) * ENNReal.ofReal (rho / (4 * ((T.card : ℝ) + 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal rho := aux_prop_quenched_convergence_arith_sum T.card hrho

end QuenchedConvergenceHelpers

/-- Proposition `mfd:prop-quenched-convergence` (paper 5251-5283), "Convergence
of quenched laws": the quenched path laws are Cauchy IN PROBABILITY, locally
uniformly in the starting point, along the FULL sequence, and the limit is a
continuous random kernel.  The paper's `sup_{x ∈ B} d_weak > eps` is written
`∃ x ∈ B, eps ≤ d_weak`, which avoids presupposing measurability of a supremum
over an uncountable starting set; the two events differ only where the supremum
is attained in the limit, and every use is through Markov's inequality with
`eps` ranging over a dense set.  Deviation: `DEV-010` Departure 3.

`hin` ties the approximating kernels to the model's cutoff-`N` semigroups.
`hlim` is the statement that `K` is the path law of `P`; the paper DEFINES the
limit kernel as the limit of the quenched laws, so the conclusion is what
identifies it.

Inputs consumed: the countable family of determining functionals `Psi_m` and
`mfd:lem-determining`; the compact set of laws from `mfd:lem-tightness`, on
which `Pm ↦ (∫ Psi_m dPm)_m` is a homeomorphism onto its image (5261-5266); and
the Cauchy-in-probability property of the right-hand side of `eq:mfd-44`, which
is `mfd:lem-random-input` applied `k` times from the inside out (5267-5270),
supplied here as `hcauchy`. 
The conclusion is the paper's DOUBLE-SEQUENCE Cauchy statement, between two
cutoffs, and no limiting kernel appears in it.  An earlier version measured the
distance to a free binder `K` constrained only by `IsMarkovKernel`; that is
refutable, since it asserts convergence to EVERY Markov kernel.  The limiting
kernel is produced from this Cauchy property by `\noderef{limit_kernel}`, which
is where completeness of the space of laws is used.
-/
theorem prop_quenched_convergence
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (hcauchy : ∀ (k : ℕ) (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (n : Fin k → ℕ) (B : Set (SpatialCoordinates d)), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
        (chaosSampleLaw M).toMeasure
            {omega : BilateralField d | ∃ x ∈ B, eps ≤
              |(∫ path, (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
                  Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
                    ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
                  ∂(KN N (omega, x))) -
                (∫ path, (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
                  Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
                    ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
                  ∂(KN N' (omega, x)))|} ≤ ENNReal.ofReal rho)
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
          ∀ N : ℕ,
            (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
              ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal epsilon) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
          (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                  (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
            ENNReal.ofReal rho := by
  intro B hB eps heps rho hrho
  exact aux_prop_quenched_convergence_main (chaosSampleLaw M).toMeasure KN hKN hcauchy htight
    B hB eps heps rho hrho

end Paper
