module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import SubdiffusiveProcess.Paper.tight_whole_space_resolvent_limit
public import SubdiffusiveProcess.Paper.whole_space_resolvent_localization

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section RandomInputCapacity

open Set



/-! #### Capacity -/
/-- One step of the capacitability construction: cutting the `k`-th coordinate at a finite
bound loses arbitrarily little outer measure of the image. -/
theorem aux_lem_random_input_cut_step {α : Type*} [MeasurableSpace α]
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
  push Not at hcon
  have hfin : μ (f '' S) ≠ ∞ := measure_ne_top μ _
  have hpos : μ (f '' S) ≠ 0 := by
    have := hcon 0
    exact (lt_of_le_of_lt (zero_le) this).ne'
  have hle : μ (f '' S) ≤ μ (f '' S) - η := by
    conv_lhs => rw [hsup]
    refine iSup_le fun b => ?_
    exact ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top hfin
      (le_add_self.trans (hcon b).le)) (hcon b).le
  exact absurd hle (not_le.2 (ENNReal.sub_lt_self hfin hpos hη))

/-- The compactness step of capacitability: points in the closures of all truncated images
lie in the image of the limiting compact box. -/
theorem aux_lem_random_input_closure_box {α : Type*} [TopologicalSpace α] [T2Space α]
    [TopologicalSpace.PseudoMetrizableSpace α] (f : (ℕ → ℕ) → α) (hf : Continuous f)
    (m : ℕ → ℕ) (y : α)
    (hy : ∀ n : ℕ, y ∈ closure (f '' {s : ℕ → ℕ | ∀ i < n, s i ≤ m i})) :
    y ∈ f '' {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
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
      ext s; simp only [mem_ofPred_eq, Set.mem_pi, mem_univ, mem_Iic, true_implies]
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
theorem aux_lem_random_input_analytic_inner {α : Type*} [TopologicalSpace α]
    [T2Space α] [TopologicalSpace.PseudoMetrizableSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : (ℕ → ℕ) → α) (hf : Continuous f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ L : Set α, IsClosed L ∧ L ⊆ range f ∧ μ (range f) ≤ μ L + ε := by
  classical
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε ℕ
  have hstep : ∀ (S : Set (ℕ → ℕ)) (k : ℕ), ∃ b : ℕ,
      μ (f '' S) ≤ μ (f '' (S ∩ {s | s k ≤ b})) + (ε' k : ℝ≥0∞) := fun S k =>
    aux_lem_random_input_cut_step μ f S k
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
      simp only [mem_inter_iff, mem_ofPred_eq]
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
      ext s; simp only [mem_ofPred_eq, Set.mem_pi, mem_univ, mem_Iic, true_implies]
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
    refine aux_lem_random_input_closure_box f hf m y (fun n => ?_)
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
theorem aux_lem_random_input_analytic_nullMeasurable {α : Type*}
    [TopologicalSpace α] [T2Space α] [TopologicalSpace.PseudoMetrizableSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {A : Set α} (hA : AnalyticSet A) : NullMeasurableSet A μ := by
  rw [AnalyticSet_def] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact nullMeasurableSet_empty
  have hchoose : ∀ n : ℕ, ∃ L : Set α, IsClosed L ∧ L ⊆ range f ∧
      μ (range f) ≤ μ L + ((n : ℝ≥0∞) + 1)⁻¹ := fun n =>
    aux_lem_random_input_analytic_inner μ f hf (by simp)
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
    have hsplit := measure_inter_add_sdiff (range f) hUm (μ := μ)
    rw [inter_eq_right.2 hUsub] at hsplit
    have hfin : μ U ≠ ∞ := measure_ne_top μ _
    have : μ (range f \ U) ≤ 0 := by
      have h1 : μ U + μ (range f \ U) ≤ μ U + 0 := by
        rw [hsplit, add_zero]; exact hle
      exact (ENNReal.add_le_add_iff_left hfin).1 h1
    exact le_antisymm this (zero_le)
  have : range f = U ∪ (range f \ U) := (union_sdiff_cancel hUsub).symm
  rw [this]
  exact hUm.nullMeasurableSet.union (NullMeasurableSet.of_null hdiff)

/-- Markov's inequality for an uncountable-supremum event.  The event `∃ x ∈ B, c < F (ω, x)`
is the projection of a Borel set of a Polish product, hence analytic, hence null-measurable;
so its outer measure is controlled by the (lower) integral of the supremum. -/
theorem aux_lem_random_input_markov_sup {Ω X : Type*}
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
  have hAnull := aux_lem_random_input_analytic_nullMeasurable μ hAan
  obtain ⟨T, hTA, hTm, hTae⟩ := hAnull.exists_measurable_subset_ae_eq
  rw [← measure_congr hTae, ← lintegral_indicator_const hTm c]
  refine lintegral_mono fun ω => ?_
  by_cases hω : ω ∈ T
  · rw [indicator_of_mem hω]
    obtain ⟨x, hx, hc⟩ := hTA hω
    exact hc.le.trans (le_iSup₂ (f := fun x (_ : x ∈ B) => F (ω, x)) x hx)
  · rw [indicator_of_notMem hω]; exact zero_le

end RandomInputCapacity

/-- The discounted occupation functional of one path is bounded by `‖h‖ / n`. -/
theorem aux_lem_random_input_path_bound {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (h : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) :
    |∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) * h (path (Real.toNNReal t))| ≤
      ‖h‖ / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Real.exp (-(n : ℝ) * t) * h (path (Real.toNNReal t))‖ ≤
        ‖h‖ * Real.exp (-(n : ℝ) * t) := by
    filter_upwards with t
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm _) (Real.exp_pos _).le
  have h_major : Integrable (fun t : ℝ => ‖h‖ * Real.exp (-(n : ℝ) * t))
      (volume.restrict (Set.Ioi (0 : ℝ))) := (exp_neg_integrableOn_Ioi 0 hnpos).const_mul ‖h‖
  have h_int := norm_integral_le_of_norm_le h_major h_bound
  rw [integral_const_mul,
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero
      hnpos, ← div_eq_mul_inv] at h_int
  rwa [Real.norm_eq_abs] at h_int

/-- If the datum is `δ`-small along the path up to time `T`, the occupation functional is
bounded by `δ / n` plus an exponentially small tail. -/
theorem aux_lem_random_input_path_local_bound {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (h : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d)
    (D δ T : ℝ) (hD : ‖h‖ ≤ D) (hδ : 0 ≤ δ)
    (hclose : ∀ s : ℝ≥0, (s : ℝ) ≤ T → |h (path s)| ≤ δ) :
    |∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) * h (path (Real.toNNReal t))| ≤
      δ / n + 2 * D * Real.exp (-(n : ℝ) * T / 2) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) / 2 := by positivity
  have hD0 : 0 ≤ D := (norm_nonneg h).trans hD
  let m : ℝ → ℝ := fun t => δ * Real.exp (-(n : ℝ) * t) +
    D * Real.exp (-(n : ℝ) * T / 2) * Real.exp (-((n : ℝ) / 2) * t)
  have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Real.exp (-(n : ℝ) * t) * h (path (Real.toNNReal t))‖ ≤ m t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht0 : 0 < t := ht
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs]
    have hA : 0 ≤ D * Real.exp (-(n : ℝ) * T / 2) * Real.exp (-((n : ℝ) / 2) * t) := by
      positivity
    have hB : 0 ≤ δ * Real.exp (-(n : ℝ) * t) := by positivity
    by_cases htT : t ≤ T
    · have hs : ((Real.toNNReal t : ℝ≥0) : ℝ) ≤ T := by
        rw [Real.coe_toNNReal t ht0.le]; exact htT
      have h1 := hclose _ hs
      have h2 : Real.exp (-(n : ℝ) * t) * |h (path (Real.toNNReal t))| ≤
          δ * Real.exp (-(n : ℝ) * t) := by
        rw [mul_comm δ]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      simp only [m]; linarith
    · push Not at htT
      have h1 : |h (path (Real.toNNReal t))| ≤ D := by
        rw [← Real.norm_eq_abs]; exact (h.norm_coe_le_norm _).trans hD
      have hnt : (n : ℝ) * T < (n : ℝ) * t := mul_lt_mul_of_pos_left htT hnpos
      have h2 : Real.exp (-(n : ℝ) * t) ≤
          Real.exp (-(n : ℝ) * T / 2) * Real.exp (-((n : ℝ) / 2) * t) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      calc Real.exp (-(n : ℝ) * t) * |h (path (Real.toNNReal t))|
          ≤ Real.exp (-(n : ℝ) * t) * D := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ ≤ Real.exp (-(n : ℝ) * T / 2) * Real.exp (-((n : ℝ) / 2) * t) * D :=
            mul_le_mul_of_nonneg_right h2 hD0
        _ = D * Real.exp (-(n : ℝ) * T / 2) * Real.exp (-((n : ℝ) / 2) * t) := by ring
        _ ≤ m t := by simp only [m]; linarith
  have hi1 : Integrable (fun t : ℝ => δ * Real.exp (-(n : ℝ) * t))
      (volume.restrict (Set.Ioi 0)) :=
    (exp_neg_integrableOn_Ioi 0 hnpos).const_mul δ
  have hi2 : Integrable
      (fun t : ℝ => D * Real.exp (-(n : ℝ) * T / 2) * Real.exp (-((n : ℝ) / 2) * t))
      (volume.restrict (Set.Ioi 0)) := (exp_neg_integrableOn_Ioi 0 hn2).const_mul _
  have h_int := norm_integral_le_of_norm_le (hi1.add hi2) h_bound
  have hval : ∫ t in Set.Ioi (0 : ℝ), m t =
      δ / n + 2 * D * Real.exp (-(n : ℝ) * T / 2) / n := by
    simp only [m]
    rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
      MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero
        hnpos,
      MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero
        hn2]
    field_simp
  rw [Real.norm_eq_abs] at h_int
  exact h_int.trans (le_of_eq hval)

/-- The actual cutoff resolvent is a contraction: `|RN f| ≤ ‖f‖ / n`. -/
theorem aux_lem_random_input_rn_bound {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : ℕ → BilateralField d → ℕ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega n f x, RN N omega n f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (N : ℕ) (omega : BilateralField d) (n : ℕ) (hn : 1 ≤ n)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    |RN N omega n f x| ≤ ‖f‖ / n := by
  have := (hKN N).isProbabilityMeasure (omega, x)
  rw [hRN, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_const (‖f‖ / n))
    (Filter.Eventually.of_forall fun path => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs]; exact aux_lem_random_input_path_bound n hn f path
  · simp

/-- Pathwise localization of the difference of two actual cutoff resolvents: closeness of the
data along the paths of `A` up to time `T` costs `δ / n`, the time tail is exponentially small,
and the paths outside `A` cost `D / n` times their probability. -/
theorem aux_lem_random_input_rn_diff {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : ℕ → BilateralField d → ℕ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega n f x, RN N omega n f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (N : ℕ) (omega : BilateralField d) (n : ℕ) (hn : 1 ≤ n) (x : SpatialCoordinates d)
    (f1 f2 : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (D δ T : ℝ) (hD : ‖f1 - f2‖ ≤ D) (hδ : 0 ≤ δ)
    (A : Set (DiffusionPath d)) (hA : MeasurableSet A)
    (hclose : ∀ path ∈ A, ∀ s : ℝ≥0, (s : ℝ) ≤ T → |f1 (path s) - f2 (path s)| ≤ δ) :
    |RN N omega n f1 x - RN N omega n f2 x| ≤
      δ / n + 2 * D * Real.exp (-(n : ℝ) * T / 2) / n +
        D / n * ((KN N (omega, x)) Aᶜ).toReal := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have := (hKN N).isProbabilityMeasure (omega, x)
  let Φ : BoundedContinuousFunction (SpatialCoordinates d) ℝ → DiffusionPath d → ℝ :=
    fun f path => ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))
  have hΦint : ∀ f, Integrable (Φ f) (KN N (omega, x)) := fun f =>
    Integrable.of_bound
      (_root_.SubdiffusiveProcess.Paper.aux_tight_whole_space_resolvent_limit_occupation_stronglyMeasurable
        (n : ℝ) f).aestronglyMeasurable
      (‖f‖ / n) (Filter.Eventually.of_forall fun path => by
        rw [Real.norm_eq_abs]; exact aux_lem_random_input_path_bound n hn f path)
  have hsub : ∀ path, Φ f1 path - Φ f2 path = Φ (f1 - f2) path := by
    intro path
    have hi : ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Integrable (fun t : ℝ => Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t)))
          (volume.restrict (Set.Ioi 0)) := by
      intro f
      refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hnpos).const_mul ‖f‖) ?_ ?_
      · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          (f.continuous.comp (path.continuous.comp
            continuous_real_toNNReal))).aestronglyMeasurable
      · filter_upwards with t
        rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), mul_comm]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (Real.exp_pos _).le
    simp only [Φ]
    rw [← integral_sub (hi f1) (hi f2)]
    congr 1
    funext t
    simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
    ring
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  have ha0 : 0 ≤ δ / n + 2 * D * Real.exp (-(n : ℝ) * T / 2) / n := by positivity
  have hpt : ∀ path, ‖Φ (f1 - f2) path‖ ≤
      (δ / n + 2 * D * Real.exp (-(n : ℝ) * T / 2) / n) +
        Aᶜ.indicator (fun _ => D / n) path := by
    intro path
    rw [Real.norm_eq_abs]
    by_cases hpA : path ∈ A
    · rw [Set.indicator_of_notMem (by simpa using hpA), add_zero]
      exact aux_lem_random_input_path_local_bound n hn (f1 - f2) path D δ T hD hδ
        (fun s hs => by simpa using hclose path hpA s hs)
    · rw [Set.indicator_of_mem (by simpa using hpA)]
      have h1 := aux_lem_random_input_path_bound n hn (f1 - f2) path
      have h2 : ‖f1 - f2‖ / n ≤ D / n := div_le_div_of_nonneg_right hD hnpos.le
      linarith
  have hint1 : Integrable (fun _ : DiffusionPath d =>
      δ / n + 2 * D * Real.exp (-(n : ℝ) * T / 2) / n) (KN N (omega, x)) := integrable_const _
  have hint2 : Integrable (fun path : DiffusionPath d => Aᶜ.indicator (fun _ => D / n) path)
      (KN N (omega, x)) := (integrable_const (D / n)).indicator hA.compl
  have hmain := norm_integral_le_of_norm_le (hint1.add hint2) (Filter.Eventually.of_forall hpt)
  simp only [Pi.add_apply] at hmain
  rw [integral_add hint1 hint2, integral_const, integral_indicator_const _ hA.compl] at hmain
  rw [hRN, hRN]
  change |∫ path, Φ f1 path ∂(KN N (omega, x)) - ∫ path, Φ f2 path ∂(KN N (omega, x))| ≤ _
  rw [← integral_sub (hΦint f1) (hΦint f2)]
  simp_rw [hsub]
  rw [← Real.norm_eq_abs]
  refine hmain.trans (le_of_eq ?_)
  simp only [smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one, one_mul]
  ring

/-- The actual cutoff resolvent of a measurable random datum is measurable in the
environment, at every point. -/
theorem aux_lem_random_input_random_eval_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : ℕ → BilateralField d → ℕ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega n f x, RN N omega n f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (N n : ℕ) (g : BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hg : Measurable fun omega => (g omega).toContinuousMap) (x : SpatialCoordinates d) :
    Measurable fun omega => RN N omega n (g omega) x := by
  have := hKN N
  let Ψ : C(SpatialCoordinates d, ℝ) × DiffusionPath d → ℝ := fun p =>
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) * p.1 (p.2 (Real.toNNReal t))
  have hcont : Continuous (fun q : (C(SpatialCoordinates d, ℝ) × DiffusionPath d) × ℝ =>
      Real.exp (-(n : ℝ) * q.2) * q.1.1 (q.1.2 (Real.toNNReal q.2))) := by
    have hpath : Continuous (fun q : (C(SpatialCoordinates d, ℝ) × DiffusionPath d) × ℝ =>
        q.1.2 (Real.toNNReal q.2)) :=
      continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
        (continuous_real_toNNReal.comp continuous_snd))
    have hval : Continuous (fun q : (C(SpatialCoordinates d, ℝ) × DiffusionPath d) × ℝ =>
        q.1.1 (q.1.2 (Real.toNNReal q.2))) :=
      continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk hpath)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul hval
  have hΨ : StronglyMeasurable Ψ := hcont.measurable.stronglyMeasurable.integral_prod_right'
  have hF : StronglyMeasurable
      (fun q : (BilateralField d × SpatialCoordinates d) × DiffusionPath d =>
        Ψ ((g q.1.1).toContinuousMap, q.2)) :=
    hΨ.comp_measurable ((hg.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hker : StronglyMeasurable (fun a : BilateralField d × SpatialCoordinates d =>
      ∫ path, Ψ ((g a.1).toContinuousMap, path) ∂(KN N a)) :=
    hF.integral_kernel_prod_right'
  have hfun : (fun omega => RN N omega n (g omega) x) =
      (fun a : BilateralField d × SpatialCoordinates d =>
        ∫ path, Ψ ((g a.1).toContinuousMap, path) ∂(KN N a)) ∘ (fun omega => (omega, x)) := by
    funext omega
    rw [hRN]
    rfl
  rw [hfun]
  exact hker.measurable.comp measurable_prodMk_right

/-- Clipping at level `C` does not increase the distance to a value in `[-C, C]`. -/
theorem aux_lem_random_input_clip (C a b : ℝ) (hb : |b| ≤ C) :
    |max (-C) (min C a) - b| ≤ |a - b| := by
  rw [abs_le] at hb
  rcases le_total a C with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-C) a with h2 | h2
    · rw [max_eq_right h2]
    · rw [max_eq_left h2, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith

/-- A countable family of deterministic data of norm at most `C` that approximates every
datum of norm at most `C` uniformly on every compact set (compact-open separability). -/
theorem aux_lem_random_input_net {d : ℕ} (C : ℝ) (hC : 0 ≤ C) :
    ∃ h : ℕ → BoundedContinuousFunction (SpatialCoordinates d) ℝ, (∀ k, ‖h k‖ ≤ C) ∧
      ∀ u : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖u‖ ≤ C →
        ∀ K : Set (SpatialCoordinates d), IsCompact K → ∀ eta : ℝ, 0 < eta →
          ∃ k, ∀ y ∈ K, |u y - h k y| < eta := by
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq C(SpatialCoordinates d, ℝ)
  have hclipc : ∀ k, Continuous (fun y => max (-C) (min C (q k y))) := fun k =>
    continuous_const.max (continuous_const.min (q k).continuous)
  have hclipb : ∀ k y, ‖max (-C) (min C (q k y))‖ ≤ C := by
    intro k y
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  let h : ℕ → BoundedContinuousFunction (SpatialCoordinates d) ℝ := fun k =>
    BoundedContinuousFunction.ofNormedAddCommGroup _ (hclipc k) C (hclipb k)
  refine ⟨h, fun k => BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hC _, ?_⟩
  intro u hu K hK eta heta
  have hU : {fg : C(SpatialCoordinates d, ℝ) × C(SpatialCoordinates d, ℝ) |
      ∀ x ∈ K, (fg.1 x, fg.2 x) ∈ {p : ℝ × ℝ | dist p.1 p.2 < eta}} ∈
        uniformity C(SpatialCoordinates d, ℝ) :=
    ContinuousMap.hasBasis_compactConvergenceUniformity.mem_of_mem
      (i := (K, {p : ℝ × ℝ | dist p.1 p.2 < eta})) ⟨hK, Metric.dist_mem_uniformity heta⟩
  have hnhds := UniformSpace.ball_mem_nhds u.toContinuousMap hU
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hq.inter_nhds_nonempty hnhds
  refine ⟨k, fun y hy => ?_⟩
  have hky : dist (u y) (q k y) < eta := hk y hy
  rw [Real.dist_eq] at hky
  have huy : |u y| ≤ C := by rw [← Real.norm_eq_abs]; exact (u.norm_coe_le_norm y).trans hu
  have hclip := aux_lem_random_input_clip C (q k y) (u y) huy
  change |u y - max (-C) (min C (q k y))| < eta
  rw [abs_sub_comm]
  calc |max (-C) (min C (q k y)) - u y| ≤ |q k y - u y| := hclip
    _ = |u y - q k y| := abs_sub_comm _ _
    _ < eta := hky

/-- A countable measurable cover has finite subcovers up to arbitrarily small measure. -/
theorem aux_lem_random_input_finite_cover {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : ℕ → Set Ω) (hS : ∀ k, MeasurableSet (S k))
    (hcover : ∀ ω, ∃ k, ω ∈ S k) (rho : ℝ) (hrho : 0 < rho) :
    ∃ m : ℕ, μ {ω | ∀ k < m, ω ∉ S k} ≤ ENNReal.ofReal rho := by
  let E : ℕ → Set Ω := fun m => {ω | ∀ k < m, ω ∉ S k}
  have hEmeas : ∀ m, MeasurableSet (E m) := by
    intro m
    have : E m = ⋂ k ∈ Finset.range m, (S k)ᶜ := by
      ext ω; simp [E]
    rw [this]
    exact Finset.measurableSet_biInter _ fun k _ => (hS k).compl
  have hanti : Antitone E := fun a b hab ω hω k hk => hω k (lt_of_lt_of_le hk hab)
  have hempty : (⋂ m, E m) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, hk⟩ := hcover ω
    exact ⟨k + 1, fun h => h k (Nat.lt_succ_self k) hk⟩
  have htend := tendsto_measure_iInter_atTop (μ := μ)
    (fun m => (hEmeas m).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
  rw [hempty, measure_empty] at htend
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal rho := ENNReal.ofReal_pos.mpr hrho
  obtain ⟨m, hm⟩ := (htend.eventually (gt_mem_nhds hpos)).exists
  exact ⟨m, hm.le⟩

/-- Five fifths. -/
theorem aux_lem_random_input_ofReal_five (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (r / 5) + ENNReal.ofReal (r / 5) + ENNReal.ofReal (r / 5) +
      ENNReal.ofReal (r / 5) + ENNReal.ofReal (r / 5) = ENNReal.ofReal r := by
  have h5 : 0 ≤ r / 5 := by positivity
  rw [← ENNReal.ofReal_add h5 h5, ← ENNReal.ofReal_add (by positivity) h5,
    ← ENNReal.ofReal_add (by positivity) h5, ← ENNReal.ofReal_add (by positivity) h5]
  congr 1
  ring

/-- Three thirds. -/
theorem aux_lem_random_input_ofReal_three (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (r / 3) + ENNReal.ofReal (r / 3) + ENNReal.ofReal (r / 3) =
      ENNReal.ofReal r := by
  have h3 : 0 ≤ r / 3 := by positivity
  rw [← ENNReal.ofReal_add h3 h3, ← ENNReal.ofReal_add (by positivity) h3]
  congr 1
  ring

/-- Localization in probability of differences of actual cutoff resolvents, uniformly in the
cutoff: data that are uniformly `D`-close and `eta`-close on one compact set `K` give
resolvents that are `eps`-close on `B`, outside an event of probability at most `rho`.  The
compact set of paths comes from the frozen averaged compact-containment premise; the event is
controlled by the analytic-set Markov inequality. -/
theorem aux_lem_random_input_local_diff {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsFiniteMeasure μ]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : ℕ → BilateralField d → ℕ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega n f x, RN N omega n f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ A : Set (DiffusionPath d), IsCompact A ∧
        ∀ N,
          (∫⁻ omega, ⨆ x : B, KN N (omega, x.val) Aᶜ ∂μ) ≤ ENNReal.ofReal eps)
    (n : ℕ) (hn : 1 ≤ n) (B : Set (SpatialCoordinates d)) (hB : IsCompact B)
    (eps rho D : ℝ) (heps : 0 < eps) (hrho : 0 < rho) (hD : 0 ≤ D) :
    ∃ K : Set (SpatialCoordinates d), IsCompact K ∧ ∃ eta : ℝ, 0 < eta ∧ ∀ N,
      μ {omega | ∃ f1 f2 : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ‖f1 - f2‖ ≤ D ∧ (∀ y ∈ K, |f1 y - f2 y| ≤ eta) ∧
        ∃ x ∈ B, eps ≤ |RN N omega n f1 x - RN N omega n f2 x|} ≤ ENNReal.ofReal rho := by
  classical
  have : PolishSpace (BilateralField d) := {}
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD1 : 0 < D + 1 := by linarith
  have hDD : D / (D + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) hD1.le
  let c : ℝ := eps / (4 * (D + 1))
  have hc : 0 < c := by positivity
  have hDc : D * c ≤ eps / 4 := by
    calc D * c = eps / 4 * (D / (D + 1)) := by simp only [c]; field_simp
      _ ≤ eps / 4 * 1 := mul_le_mul_of_nonneg_left hDD (by positivity)
      _ = eps / 4 := mul_one _
  have hlim : Tendsto (fun T : ℝ => Real.exp (-(n : ℝ) * T / 2)) atTop (𝓝 0) := by
    have h1 := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show -(n : ℝ) / 2 < 0 by linarith))
    refine h1.congr (fun T => ?_)
    simp only [Function.comp, id]
    ring_nf
  have hsmall : (0 : ℝ) < eps / (8 * (D + 1)) := by positivity
  obtain ⟨T, hT0, hTs⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds hsmall))).exists
  have hTail : 2 * D * Real.exp (-(n : ℝ) * T / 2) ≤ eps / 4 := by
    calc 2 * D * Real.exp (-(n : ℝ) * T / 2) ≤ 2 * D * (eps / (8 * (D + 1))) :=
          mul_le_mul_of_nonneg_left hTs.le (by positivity)
      _ = eps / 4 * (D / (D + 1)) := by field_simp; ring
      _ ≤ eps / 4 * 1 := mul_le_mul_of_nonneg_left hDD (by positivity)
      _ = eps / 4 := mul_one _
  obtain ⟨A, hAc, hAt⟩ := htight B hB (c * rho) (by positivity)
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  let K : Set (SpatialCoordinates d) :=
    (fun q : DiffusionPath d × ℝ≥0 => q.1 q.2) '' (A ×ˢ Set.Icc 0 (Real.toNNReal T))
  have hK : IsCompact K := (hAc.prod isCompact_Icc).image continuous_eval
  refine ⟨K, hK, eps / 4, by positivity, fun N => ?_⟩
  have hsub : {omega | ∃ f1 f2 : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ‖f1 - f2‖ ≤ D ∧ (∀ y ∈ K, |f1 y - f2 y| ≤ eps / 4) ∧
      ∃ x ∈ B, eps ≤ |RN N omega n f1 x - RN N omega n f2 x|} ⊆
      {omega | ∃ x ∈ B, ENNReal.ofReal c < KN N (omega, x) Aᶜ} := by
    rintro omega ⟨f1, f2, hf12, hfK, x, hx, hlarge⟩
    by_contra hnot
    have hle : KN N (omega, x) Aᶜ ≤ ENNReal.ofReal c := by
      by_contra h
      exact hnot ⟨x, hx, lt_of_not_ge h⟩
    have hreal : (KN N (omega, x) Aᶜ).toReal ≤ c := ENNReal.toReal_le_of_le_ofReal hc.le hle
    have hdiff := aux_lem_random_input_rn_diff KN hKN RN hRN N omega n hn x f1 f2 D (eps / 4) T
      hf12 (by positivity) A hAm (fun path hp s hs => by
        refine hfK _ ⟨(path, s), Set.mk_mem_prod hp ⟨zero_le, ?_⟩, rfl⟩
        rw [← Real.toNNReal_coe (r := s)]
        exact Real.toNNReal_le_toNNReal hs)
    have e1 : eps / 4 / n ≤ eps / 4 := div_le_self (by positivity) hn1
    have e2 : 2 * D * Real.exp (-(n : ℝ) * T / 2) / n ≤ 2 * D * Real.exp (-(n : ℝ) * T / 2) :=
      div_le_self (by positivity) hn1
    have e3 : D / n * (KN N (omega, x) Aᶜ).toReal ≤ D * c :=
      mul_le_mul (div_le_self hD hn1) hreal ENNReal.toReal_nonneg hD
    linarith
  have hM := aux_lem_random_input_markov_sup μ
    (fun p : BilateralField d × SpatialCoordinates d => KN N p Aᶜ)
    ((KN N).measurable_coe hAm.compl) B hB.isClosed.measurableSet (ENNReal.ofReal c)
  have hint : ∫⁻ omega, ⨆ x ∈ B, KN N (omega, x) Aᶜ ∂μ ≤ ENNReal.ofReal (c * rho) := by
    have heq : ∀ omega, (⨆ x ∈ B, KN N (omega, x) Aᶜ) = ⨆ x : B, KN N (omega, x.val) Aᶜ :=
      fun omega => (iSup_subtype'' B (fun x => KN N (omega, x) Aᶜ)).symm
    rw [lintegral_congr heq]
    exact hAt N
  have hmul : ENNReal.ofReal c * μ {omega | ∃ x ∈ B, ENNReal.ofReal c < KN N (omega, x) Aᶜ} ≤
      ENNReal.ofReal c * ENNReal.ofReal rho := by
    rw [← ENNReal.ofReal_mul hc.le]
    exact hM.trans hint
  have hcancel := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hc).ne'
    ENNReal.ofReal_ne_top).mp hmul
  exact (measure_mono hsub).trans hcancel

/-- Compact-local Cauchy in probability for the actual cutoff resolvents of a measurable,
uniformly bounded random datum: approximate the datum on one compact set by finitely many
deterministic data, localize, and use deterministic convergence for those finitely many. -/
theorem aux_lem_random_input_cauchy {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsFiniteMeasure μ]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : ℕ → BilateralField d → ℕ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega n f x, RN N omega n f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ A : Set (DiffusionPath d), IsCompact A ∧
        ∀ N,
          (∫⁻ omega, ⨆ x : B, KN N (omega, x.val) Aᶜ ∂μ) ≤ ENNReal.ofReal eps)
    (R : ℕ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      BilateralField d → C(SpatialCoordinates d, ℝ))
    (hdet : ∀ n, 1 ≤ n → ∀ f,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0, ∀ N, N0 ≤ N →
          μ {omega | ∃ x ∈ B, eps ≤ |RN N omega n f x - R n f omega x|} ≤
            ENNReal.ofReal rho)
    (n : ℕ) (hn : 1 ≤ n)
    (g : BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hg : Measurable fun omega => (g omega).toContinuousMap)
    (Cg : ℝ) (hCg : 0 ≤ Cg) (hgb : ∀ omega, ‖g omega‖ ≤ Cg) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N P, N0 ≤ N → N0 ≤ P →
        μ {omega | ∃ x ∈ B,
          eps ≤ |RN N omega n (g omega) x - RN P omega n (g omega) x|} ≤
          ENNReal.ofReal rho := by
  classical
  intro B hB eps heps rho hrho
  obtain ⟨K, hK, eta, heta, hloc⟩ := aux_lem_random_input_local_diff μ KN hKN RN hRN htight
    n hn B hB (eps / 4) (rho / 5) (2 * Cg) (by positivity) (by positivity) (by positivity)
  obtain ⟨h, hhb, hnet⟩ := aux_lem_random_input_net (d := d) Cg hCg
  let S : ℕ → Set (BilateralField d) := fun k =>
    {omega | ∀ y ∈ K, |g omega y - h k y| ≤ eta}
  have hS : ∀ k, MeasurableSet (S k) := by
    intro k
    have hclosed : IsClosed
        {v : C(SpatialCoordinates d, ℝ) | ∀ y ∈ K, |v y - h k y| ≤ eta} := by
      simp only [Set.ofPred_forall]
      exact isClosed_biInter fun y _ => isClosed_le
        (continuous_abs.comp ((continuous_eval_const y).sub continuous_const)) continuous_const
    exact hg hclosed.measurableSet
  have hcover : ∀ omega, ∃ k, omega ∈ S k := by
    intro omega
    obtain ⟨k, hk⟩ := hnet (g omega) (hgb omega) K hK eta heta
    exact ⟨k, fun y hy => (hk y hy).le⟩
  obtain ⟨m, hm⟩ := aux_lem_random_input_finite_cover μ S hS hcover (rho / 5) (by positivity)
  have hsel : ∀ k : ℕ, ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      μ {omega | ∃ x ∈ B, eps / 4 ≤ |RN N omega n (h k) x - R n (h k) omega x|} ≤
        ENNReal.ofReal (rho / (5 * (m + 1))) :=
    fun k => hdet n hn (h k) B hB (eps / 4) (by positivity) _ (by positivity)
  choose N0 hN0 using hsel
  refine ⟨(Finset.range m).sup N0, fun N P hN hP => ?_⟩
  let Loc : ℕ → Set (BilateralField d) := fun N =>
    {omega | ∃ f1 f2 : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ‖f1 - f2‖ ≤ 2 * Cg ∧ (∀ y ∈ K, |f1 y - f2 y| ≤ eta) ∧
      ∃ x ∈ B, eps / 4 ≤ |RN N omega n f1 x - RN N omega n f2 x|}
  let Det : ℕ → ℕ → Set (BilateralField d) := fun N k =>
    {omega | ∃ x ∈ B, eps / 4 ≤ |RN N omega n (h k) x - R n (h k) omega x|}
  let E : Set (BilateralField d) := {omega | ∀ k < m, omega ∉ S k}
  have hDetU : ∀ N', (Finset.range m).sup N0 ≤ N' →
      μ (⋃ k ∈ Finset.range m, Det N' k) ≤ ENNReal.ofReal (rho / 5) := by
    intro N' hN'
    calc μ (⋃ k ∈ Finset.range m, Det N' k) ≤ ∑ k ∈ Finset.range m, μ (Det N' k) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range m, ENNReal.ofReal (rho / (5 * (m + 1))) :=
          Finset.sum_le_sum fun k hk => hN0 k N' ((Finset.le_sup hk).trans hN')
      _ = ENNReal.ofReal (m * (rho / (5 * (m + 1)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (rho / 5) := by
          apply ENNReal.ofReal_le_ofReal
          have hm1 : (m : ℝ) / (m + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
          have hmeq : (m : ℝ) * (rho / (5 * (m + 1))) = rho / 5 * ((m : ℝ) / (m + 1)) := by
            field_simp
          calc (m : ℝ) * (rho / (5 * (m + 1))) = rho / 5 * ((m : ℝ) / (m + 1)) := hmeq
            _ ≤ rho / 5 * 1 := mul_le_mul_of_nonneg_left hm1 (by positivity)
            _ = rho / 5 := mul_one _
  have hsub : {omega | ∃ x ∈ B,
      eps ≤ |RN N omega n (g omega) x - RN P omega n (g omega) x|} ⊆
      Loc N ∪ Loc P ∪ E ∪ (⋃ k ∈ Finset.range m, Det N k) ∪
        (⋃ k ∈ Finset.range m, Det P k) := by
    rintro omega ⟨x, hx, hlarge⟩
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨⟨⟨hLN, hLP⟩, hE⟩, hDN⟩, hDP⟩ := hnot
    have hEk : ∃ k < m, omega ∈ S k := by
      by_contra hcon
      push Not at hcon
      exact hE hcon
    obtain ⟨k, hkm, hkS⟩ := hEk
    have hkr : k ∈ Finset.range m := Finset.mem_range.mpr hkm
    have hnorm : ‖g omega - h k‖ ≤ 2 * Cg := by
      calc ‖g omega - h k‖ ≤ ‖g omega‖ + ‖h k‖ := norm_sub_le _ _
        _ ≤ Cg + Cg := add_le_add (hgb omega) (hhb k)
        _ = 2 * Cg := by ring
    have h1 : |RN N omega n (g omega) x - RN N omega n (h k) x| < eps / 4 := by
      by_contra hc
      exact hLN ⟨g omega, h k, hnorm, hkS, x, hx, le_of_not_gt hc⟩
    have h2 : |RN P omega n (g omega) x - RN P omega n (h k) x| < eps / 4 := by
      by_contra hc
      exact hLP ⟨g omega, h k, hnorm, hkS, x, hx, le_of_not_gt hc⟩
    have h3 : |RN N omega n (h k) x - R n (h k) omega x| < eps / 4 := by
      by_contra hc
      exact hDN (Set.mem_biUnion hkr ⟨x, hx, le_of_not_gt hc⟩)
    have h4 : |RN P omega n (h k) x - R n (h k) omega x| < eps / 4 := by
      by_contra hc
      exact hDP (Set.mem_biUnion hkr ⟨x, hx, le_of_not_gt hc⟩)
    obtain ⟨h1l, h1r⟩ := abs_lt.mp h1
    obtain ⟨h2l, h2r⟩ := abs_lt.mp h2
    obtain ⟨h3l, h3r⟩ := abs_lt.mp h3
    obtain ⟨h4l, h4r⟩ := abs_lt.mp h4
    rcases le_abs'.mp hlarge with hc | hc <;> linarith
  calc μ {omega | ∃ x ∈ B,
        eps ≤ |RN N omega n (g omega) x - RN P omega n (g omega) x|}
      ≤ μ (Loc N ∪ Loc P ∪ E ∪ (⋃ k ∈ Finset.range m, Det N k) ∪
          (⋃ k ∈ Finset.range m, Det P k)) := measure_mono hsub
    _ ≤ μ (Loc N) + μ (Loc P) + μ E + μ (⋃ k ∈ Finset.range m, Det N k) +
          μ (⋃ k ∈ Finset.range m, Det P k) := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (rho / 5) + ENNReal.ofReal (rho / 5) + ENNReal.ofReal (rho / 5) +
          ENNReal.ofReal (rho / 5) + ENNReal.ofReal (rho / 5) := by
        exact add_le_add (add_le_add (add_le_add (add_le_add (hloc N) (hloc P)) hm)
          (hDetU N hN)) (hDetU P hP)
    _ = ENNReal.ofReal rho := aux_lem_random_input_ofReal_five rho hrho.le

/-- Locally uniform limits in probability are almost surely unique. -/
theorem aux_lem_random_input_ae_unique {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    (μ : Measure Ω) (u : ℕ → Ω → X → ℝ) (v w : Ω → X → ℝ)
    (hv : ∀ B : Set X, IsCompact B → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → μ {ω | ∃ x ∈ B, eps ≤ |u N ω x - v ω x|} ≤ ENNReal.ofReal rho)
    (hw : ∀ B : Set X, IsCompact B → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → μ {ω | ∃ x ∈ B, eps ≤ |u N ω x - w ω x|} ≤ ENNReal.ofReal rho) :
    ∀ᵐ ω ∂μ, ∀ x, v ω x = w ω x := by
  let Kc := CompactExhaustion.choice X
  let Bad : ℕ → ℕ → Set Ω := fun k j =>
    {ω | ∃ x ∈ Kc k, 1 / ((j : ℝ) + 1) ≤ |v ω x - w ω x|}
  have hBad : ∀ k j, μ (Bad k j) = 0 := by
    intro k j
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hle : ∀ i : ℕ, μ (Bad k j) ≤ ENNReal.ofReal (2 * (1 / ((i : ℝ) + 1))) := by
      intro i
      have hi : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
      obtain ⟨N1, hN1⟩ := hv (Kc k) (Kc.isCompact k) _ (half_pos hj) _ hi
      obtain ⟨N2, hN2⟩ := hw (Kc k) (Kc.isCompact k) _ (half_pos hj) _ hi
      have hsub : Bad k j ⊆
          {ω | ∃ x ∈ Kc k, 1 / ((j : ℝ) + 1) / 2 ≤ |u (max N1 N2) ω x - v ω x|} ∪
          {ω | ∃ x ∈ Kc k, 1 / ((j : ℝ) + 1) / 2 ≤ |u (max N1 N2) ω x - w ω x|} := by
        rintro ω ⟨x, hx, hbig⟩
        by_contra hnot
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and,
          not_le] at hnot
        obtain ⟨a1l, a1r⟩ := abs_lt.mp (hnot.1 x hx)
        obtain ⟨a2l, a2r⟩ := abs_lt.mp (hnot.2 x hx)
        rcases le_abs'.mp hbig with hc | hc <;> linarith
      calc μ (Bad k j) ≤ _ := measure_mono hsub
        _ ≤ _ := measure_union_le _ _
        _ ≤ ENNReal.ofReal (1 / ((i : ℝ) + 1)) + ENNReal.ofReal (1 / ((i : ℝ) + 1)) :=
            add_le_add (hN1 _ (le_max_left _ _)) (hN2 _ (le_max_right _ _))
        _ = ENNReal.ofReal (2 * (1 / ((i : ℝ) + 1))) := by
            rw [← ENNReal.ofReal_add hi.le hi.le]
            congr 1
            ring
    have htend : Tendsto (fun i : ℕ => ENNReal.ofReal (2 * (1 / ((i : ℝ) + 1)))) atTop
        (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2)
      simpa using this
    exact le_antisymm (ge_of_tendsto' htend hle) (zero_le)
  have hunion : {ω | ¬ ∀ x, v ω x = w ω x} ⊆ ⋃ k, ⋃ j, Bad k j := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨x, hx⟩ := hω
    obtain ⟨k, hk⟩ := Kc.exists_mem x
    have hpos : 0 < |v ω x - w ω x| := abs_pos.mpr (sub_ne_zero.mpr hx)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨j, x, hk, hj.le⟩⟩
  rw [ae_iff]
  exact measure_mono_null hunion
    (measure_iUnion_null fun k => measure_iUnion_null fun j => hBad k j)

/-- The extension to a measurable, uniformly bounded random datum: the locally uniform limit
in probability of the actual cutoff resolvents `RN N omega n (g omega)`, taken in a bounded
continuous, measurable version with the deterministic contraction bound in every environment. -/
theorem aux_lem_random_input_exists_limit {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsProbabilityMeasure μ]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : ℕ → BilateralField d → ℕ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega n f x, RN N omega n f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (hcont : ∀ᵐ omega ∂μ, ∀ N n, 1 ≤ n → ∀ f, Continuous (RN N omega n f))
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ A : Set (DiffusionPath d), IsCompact A ∧
        ∀ N,
          (∫⁻ omega, ⨆ x : B, KN N (omega, x.val) Aᶜ ∂μ) ≤ ENNReal.ofReal eps)
    (R : ℕ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      BilateralField d → C(SpatialCoordinates d, ℝ))
    (hdet : ∀ n, 1 ≤ n → ∀ f,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0, ∀ N, N0 ≤ N →
          μ {omega | ∃ x ∈ B, eps ≤ |RN N omega n f x - R n f omega x|} ≤
            ENNReal.ofReal rho)
    (n : ℕ) (hn : 1 ≤ n)
    (g : BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hg : Measurable fun omega => (g omega).toContinuousMap)
    (Cg : ℝ) (hCg : 0 ≤ Cg) (hgb : ∀ omega, ‖g omega‖ ≤ Cg) :
    ∃ Y : BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      Measurable (fun omega => (Y omega).toContinuousMap) ∧
      (∀ C : ℝ, 0 ≤ C → (∀ omega, ‖g omega‖ ≤ C) → ∀ omega, ‖Y omega‖ ≤ C / n) ∧
      (∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
        ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
          μ {omega | ∃ x ∈ B, eps ≤ |RN N omega n (g omega) x - Y omega x|} ≤
            ENNReal.ofReal rho) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨v, φ, _hφ, hvm, hvae, hvconv⟩ := _root_.SubdiffusiveProcess.Paper.aux_tight_whole_space_resolvent_limit_completion μ
    (fun N omega x => RN N omega n (g omega) x)
    (fun N x => aux_lem_random_input_random_eval_measurable KN hKN RN hRN N n g hg x)
    (by
      filter_upwards [hcont] with omega homega N
      exact homega N n hn (g omega))
    (aux_lem_random_input_cauchy μ KN hKN RN hRN htight R hdet n hn g hg Cg hCg hgb)
  have hbdd : BddAbove (Set.range fun omega => ‖g omega‖) :=
    ⟨Cg, by rintro _ ⟨omega, rfl⟩; exact hgb omega⟩
  let s : ℝ := ⨆ omega, ‖g omega‖
  have hs_le : ∀ omega, ‖g omega‖ ≤ s := fun omega => le_ciSup hbdd omega
  have hs_min : ∀ C, (∀ omega, ‖g omega‖ ≤ C) → s ≤ C := fun C hC => ciSup_le hC
  have hs0 : 0 ≤ s / n := div_nonneg ((norm_nonneg _).trans (hs_le (fun _ => 0))) hnpos.le
  let G : Set (BilateralField d) := {omega | ∀ x, |v omega x| ≤ s / n}
  have hG : MeasurableSet G := by
    have hclosed : IsClosed {u : C(SpatialCoordinates d, ℝ) | ∀ x, |u x| ≤ s / n} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x =>
        isClosed_le (continuous_abs.comp (continuous_eval_const x)) continuous_const
    exact hvm hclosed.measurableSet
  have hGae : ∀ᵐ omega ∂μ, omega ∈ G := by
    filter_upwards [hvae] with omega homega x
    refine le_of_tendsto' ((continuous_abs.tendsto _).comp (homega x)) (fun k => ?_)
    exact (aux_lem_random_input_rn_bound KN hKN RN hRN (φ k) omega n hn (g omega) x).trans
      (div_le_div_of_nonneg_right (hs_le omega) hnpos.le)
  let Y : BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ := fun omega =>
    if h : omega ∈ G then
      BoundedContinuousFunction.mkOfBound (v omega) (2 * (s / n)) (fun x y => by
        rw [Real.dist_eq]
        have hx := h x
        have hy := h y
        calc |v omega x - v omega y| ≤ |v omega x| + |v omega y| := abs_sub _ _
          _ ≤ 2 * (s / n) := by linarith)
    else 0
  have hYcm : (fun omega => (Y omega).toContinuousMap) = G.piecewise v (fun _ => 0) := by
    funext omega
    by_cases h : omega ∈ G
    · simp only [Y, dite_eq_left h, Set.piecewise_eq_of_mem _ _ _ h]
      rfl
    · simp only [Y, dite_eq_right h, Set.piecewise_eq_of_notMem _ _ _ h]
      rfl
  have hYG : ∀ omega ∈ G, ∀ x, Y omega x = v omega x := by
    intro omega h x
    simp only [Y, dite_eq_left h]
    rfl
  refine ⟨Y, ?_, ?_, ?_⟩
  · rw [hYcm]
    exact Measurable.piecewise hG hvm measurable_const
  · intro C hC hgC omega
    by_cases h : omega ∈ G
    · have hle : ‖Y omega‖ ≤ s / n := by
        rw [BoundedContinuousFunction.norm_le hs0]
        intro x
        rw [hYG omega h x, Real.norm_eq_abs]
        exact h x
      exact hle.trans (div_le_div_of_nonneg_right (hs_min C hgC) hnpos.le)
    · simp only [Y, dite_eq_right h, norm_zero]
      exact div_nonneg hC hnpos.le
  · intro B hB eps heps rho hrho
    obtain ⟨N0, hN0⟩ := hvconv B hB eps heps rho hrho
    refine ⟨N0, fun N hN => ?_⟩
    have hnull : μ Gᶜ = 0 := by
      rw [ae_iff] at hGae
      exact hGae
    have hsub : {omega | ∃ x ∈ B, eps ≤ |RN N omega n (g omega) x - Y omega x|} ⊆
        {omega | ∃ x ∈ B, eps ≤ |RN N omega n (g omega) x - v omega x|} ∪ Gᶜ := by
      rintro omega ⟨x, hx, hbig⟩
      by_cases h : omega ∈ G
      · left
        exact ⟨x, hx, by rwa [hYG omega h x] at hbig⟩
      · right
        exact h
    calc μ {omega | ∃ x ∈ B, eps ≤ |RN N omega n (g omega) x - Y omega x|}
        ≤ μ ({omega | ∃ x ∈ B, eps ≤ |RN N omega n (g omega) x - v omega x|} ∪ Gᶜ) :=
          measure_mono hsub
      _ ≤ μ {omega | ∃ x ∈ B, eps ≤ |RN N omega n (g omega) x - v omega x|} + μ Gᶜ :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal rho + 0 := add_le_add (hN0 N hN) (le_of_eq hnull)
      _ = ENNReal.ofReal rho := add_zero _



theorem lem_random_input
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (_hin : in_crossing M H PN KN)
    (RN : ℕ → BilateralField d → ℕ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega n f x, RN N omega n f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (hcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N n, 1 ≤ n → ∀ f, Continuous (RN N omega n f))
    (R : ℕ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hRmeas : ∀ n, 1 ≤ n → ∀ f, Measurable (R n f))
    (_hRbound : ∀ n, 1 ≤ n → ∀ f,
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ x, |R n f omega x| ≤ ‖f‖ / (n : ℝ))
    (hdet : ∀ n, 1 ≤ n → ∀ f,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0, ∀ N, N0 ≤ N →
          (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ B, eps ≤ |RN N omega n f x - R n f omega x|} ≤
            ENNReal.ofReal rho)
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ A : Set (DiffusionPath d), IsCompact A ∧
        ∀ N,
          (∫⁻ omega, ⨆ x : B, KN N (omega, x.val) Aᶜ
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal eps) :
    ∃ Rrandom : ℕ →
        (BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ) →
        BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      (∀ n, 1 ≤ n → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (fun omega => (Rrandom n (fun _ => f) omega).toContinuousMap) =ᵐ[
          (chaosSampleLaw M).toMeasure] R n f) ∧
      (∀ n, 1 ≤ n →
        ∀ g : BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Measurable (fun omega => (g omega).toContinuousMap) →
        ∀ Cg : ℝ, 0 ≤ Cg →
          (∀ omega, ‖g omega‖ ≤ Cg) →
          Measurable (fun omega => (Rrandom n g omega).toContinuousMap) ∧
            ∀ omega, ‖Rrandom n g omega‖ ≤ Cg / (n : ℝ)) ∧
      (∀ (gN : ℕ → BilateralField d →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (g : BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (Cg : ℝ),
        0 ≤ Cg →
        (∀ N, Measurable (fun omega => (gN N omega).toContinuousMap)) →
        Measurable (fun omega => (g omega).toContinuousMap) →
        (∀ N omega, ‖gN N omega‖ ≤ Cg) →
        (∀ omega, ‖g omega‖ ≤ Cg) →
        (∀ B : Set (SpatialCoordinates d), IsCompact B →
          ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
            ∃ N0, ∀ N, N0 ≤ N →
              (chaosSampleLaw M).toMeasure
                {omega | ∃ x ∈ B, eps ≤ |gN N omega x - g omega x|} ≤
                ENNReal.ofReal rho) →
        ∀ n, 1 ≤ n → ∀ B : Set (SpatialCoordinates d), IsCompact B →
          ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
            ∃ N0, ∀ N, N0 ≤ N →
              (chaosSampleLaw M).toMeasure
                {omega | ∃ x ∈ B, eps ≤
                  |RN N omega n (gN N omega) x - Rrandom n g omega x|} ≤
                ENNReal.ofReal rho)
    := by
  classical
  have hmain : ∀ n : ℕ,
      ∀ g : BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∃ Y : BilateralField d → BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (1 ≤ n ∧ Measurable (fun omega => (g omega).toContinuousMap) ∧
          ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ omega, ‖g omega‖ ≤ Cg) →
        Measurable (fun omega => (Y omega).toContinuousMap) ∧
        (∀ C : ℝ, 0 ≤ C → (∀ omega, ‖g omega‖ ≤ C) → ∀ omega, ‖Y omega‖ ≤ C / n) ∧
        (∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
          ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            (chaosSampleLaw M).toMeasure
              {omega | ∃ x ∈ B, eps ≤ |RN N omega n (g omega) x - Y omega x|} ≤
              ENNReal.ofReal rho) := by
    intro n g
    by_cases hyp : 1 ≤ n ∧ Measurable (fun omega => (g omega).toContinuousMap) ∧
        ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ omega, ‖g omega‖ ≤ Cg
    · obtain ⟨hn, hg, Cg, hCg, hgb⟩ := hyp
      have hY := aux_lem_random_input_exists_limit (chaosSampleLaw M).toMeasure KN hKN RN hRN
        hcont htight R hdet n hn g hg Cg hCg hgb
      obtain ⟨Y, hY⟩ := hY
      exact ⟨Y, fun _ => hY⟩
    · exact ⟨fun _ => 0, fun h => absurd h hyp⟩
  choose Rrandom hR using hmain
  refine ⟨Rrandom, ?_, ?_, ?_⟩
  · intro n hn f
    have hgood := hR n (fun _ => f) ⟨hn, measurable_const, ‖f‖, norm_nonneg _, fun _ => le_rfl⟩
    have hu := aux_lem_random_input_ae_unique (chaosSampleLaw M).toMeasure
      (fun N omega x => RN N omega n f x) (fun omega x => Rrandom n (fun _ => f) omega x)
      (fun omega x => R n f omega x) hgood.2.2 (hdet n hn f)
    filter_upwards [hu] with omega homega
    ext x
    exact homega x
  · intro n hn g hg Cg hCg hgb
    have hgood := hR n g ⟨hn, hg, Cg, hCg, hgb⟩
    exact ⟨hgood.1, hgood.2.1 Cg hCg hgb⟩
  · intro gN g Cg hCg _hgNm hgm hgNb hgb hconv n hn B hB eps heps rho hrho
    have hgood := hR n g ⟨hn, hgm, Cg, hCg, hgb⟩
    have hloc := aux_lem_random_input_local_diff (chaosSampleLaw M).toMeasure KN hKN RN hRN
      htight n hn B hB (eps / 2) (rho / 3) (2 * Cg) (by positivity) (by positivity)
      (by positivity)
    obtain ⟨K, hK, eta, heta, hloc⟩ := hloc
    have h1 := hconv K hK eta heta (rho / 3) (by positivity)
    obtain ⟨N1, hN1⟩ := h1
    have h2 := hgood.2.2 B hB (eps / 2) (by positivity) (rho / 3) (by positivity)
    obtain ⟨N2, hN2⟩ := h2
    refine ⟨max N1 N2, fun N hN => ?_⟩
    have hsub : {omega | ∃ x ∈ B, eps ≤ |RN N omega n (gN N omega) x - Rrandom n g omega x|} ⊆
        {omega | ∃ f1 f2 : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ‖f1 - f2‖ ≤ 2 * Cg ∧ (∀ y ∈ K, |f1 y - f2 y| ≤ eta) ∧
          ∃ x ∈ B, eps / 2 ≤ |RN N omega n f1 x - RN N omega n f2 x|} ∪
        {omega | ∃ y ∈ K, eta ≤ |gN N omega y - g omega y|} ∪
        {omega | ∃ x ∈ B, eps / 2 ≤ |RN N omega n (g omega) x - Rrandom n g omega x|} := by
      rintro omega ⟨x, hx, hlarge⟩
      by_contra hnot
      simp only [Set.mem_union, not_or] at hnot
      obtain ⟨⟨hL, hC⟩, hY⟩ := hnot
      have hclose : ∀ y ∈ K, |gN N omega y - g omega y| ≤ eta := by
        intro y hy
        by_contra hc
        exact hC ⟨y, hy, (lt_of_not_ge hc).le⟩
      have hnorm : ‖gN N omega - g omega‖ ≤ 2 * Cg := by
        calc ‖gN N omega - g omega‖ ≤ ‖gN N omega‖ + ‖g omega‖ := norm_sub_le _ _
          _ ≤ Cg + Cg := add_le_add (hgNb N omega) (hgb omega)
          _ = 2 * Cg := by ring
      have a1 : |RN N omega n (gN N omega) x - RN N omega n (g omega) x| < eps / 2 := by
        by_contra hc
        exact hL ⟨gN N omega, g omega, hnorm, hclose, x, hx, le_of_not_gt hc⟩
      have a2 : |RN N omega n (g omega) x - Rrandom n g omega x| < eps / 2 := by
        by_contra hc
        exact hY ⟨x, hx, le_of_not_gt hc⟩
      obtain ⟨a1l, a1r⟩ := abs_lt.mp a1
      obtain ⟨a2l, a2r⟩ := abs_lt.mp a2
      rcases le_abs'.mp hlarge with hc | hc <;> linarith
    calc (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ B, eps ≤ |RN N omega n (gN N omega) x - Rrandom n g omega x|}
        ≤ (chaosSampleLaw M).toMeasure
            ({omega | ∃ f1 f2 : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ‖f1 - f2‖ ≤ 2 * Cg ∧ (∀ y ∈ K, |f1 y - f2 y| ≤ eta) ∧
              ∃ x ∈ B, eps / 2 ≤ |RN N omega n f1 x - RN N omega n f2 x|} ∪
            {omega | ∃ y ∈ K, eta ≤ |gN N omega y - g omega y|} ∪
            {omega | ∃ x ∈ B, eps / 2 ≤ |RN N omega n (g omega) x - Rrandom n g omega x|}) :=
          measure_mono hsub
      _ ≤ (chaosSampleLaw M).toMeasure
            {omega | ∃ f1 f2 : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ‖f1 - f2‖ ≤ 2 * Cg ∧ (∀ y ∈ K, |f1 y - f2 y| ≤ eta) ∧
              ∃ x ∈ B, eps / 2 ≤ |RN N omega n f1 x - RN N omega n f2 x|} +
          (chaosSampleLaw M).toMeasure {omega | ∃ y ∈ K, eta ≤ |gN N omega y - g omega y|} +
          (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ B, eps / 2 ≤ |RN N omega n (g omega) x - Rrandom n g omega x|} := by
          refine (measure_union_le _ _).trans ?_
          exact add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ENNReal.ofReal (rho / 3) + ENNReal.ofReal (rho / 3) + ENNReal.ofReal (rho / 3) :=
          add_le_add (add_le_add (hloc N) (hN1 N (le_trans (le_max_left _ _) hN)))
            (hN2 N (le_trans (le_max_right _ _) hN))
      _ = ENNReal.ofReal rho := aux_lem_random_input_ofReal_three rho hrho.le

end SubdiffusiveProcess.Paper
