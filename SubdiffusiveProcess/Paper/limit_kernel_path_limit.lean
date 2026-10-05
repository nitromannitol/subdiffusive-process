module

public import SubdiffusiveProcess.Paper.prop_quenched_convergence
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity


@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ### Completeness of the Lévy–Prokhorov metric and the subsequence construction

Generic helpers: the Lévy–Prokhorov metric on probability measures on a complete
second-countable metric space is complete (Cauchy ⇒ uniformly tight ⇒ a content
limit ⇒ portmanteau), and a compact-uniform Cauchy-in-probability family of
probability-law maps has a jointly measurable, a.e. continuous limit. -/
section PathLawLimitGeneric

open Metric Set
open scoped BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma aux_limit_kernel_path_limit_lp_le {P Q : ProbabilityMeasure X} {η : ℝ}
    (h : dist (LevyProkhorov.ofMeasure P) (LevyProkhorov.ofMeasure Q) < η)
    {s : Set X} (hs : MeasurableSet s) :
    (P : Measure X) s ≤ (Q : Measure X) (thickening η s) + ENNReal.ofReal η := by
  have hη : 0 ≤ η := le_trans dist_nonneg h.le
  have h' : levyProkhorovEDist (P : Measure X) (Q : Measure X) < ENNReal.ofReal η := by
    rw [← edist_lt_ofReal] at h
    exact h
  have := left_measure_le_of_levyProkhorovEDist_lt h' hs
  rwa [ENNReal.toReal_ofReal hη] at this

variable (P : ℕ → ProbabilityMeasure X)

/-- The limiting content of a Lévy–Prokhorov Cauchy sequence. -/
def aux_limit_kernel_path_limit_lam (K : Set X) : ℝ≥0∞ :=
  ⨅ k : ℕ, limsup (fun n => (P n : Measure X) (thickening (1 / ((k : ℝ) + 1)) K)) atTop

omit [BorelSpace X] in
lemma aux_limit_kernel_path_limit_lam_le_one (K : Set X) : aux_limit_kernel_path_limit_lam P K ≤ 1 := by
  refine (iInf_le _ 0).trans ?_
  refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => ?_)
  exact prob_le_one

omit [BorelSpace X] in
lemma aux_limit_kernel_path_limit_lam_ne_top (K : Set X) : aux_limit_kernel_path_limit_lam P K ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (aux_limit_kernel_path_limit_lam_le_one P K)

omit [BorelSpace X] in
lemma aux_limit_kernel_path_limit_lam_mono {K₁ K₂ : Set X} (h : K₁ ⊆ K₂) : aux_limit_kernel_path_limit_lam P K₁ ≤ aux_limit_kernel_path_limit_lam P K₂ :=
  iInf_mono fun _ => limsup_le_limsup (Eventually.of_forall fun _ =>
    measure_mono (thickening_subset_of_subset _ h))
    (by isBoundedDefault) (by isBoundedDefault)

omit [BorelSpace X] in
lemma aux_limit_kernel_path_limit_lam_le_limsup (K : Set X) {δ : ℝ} (hδ : 0 < δ) :
    aux_limit_kernel_path_limit_lam P K ≤ limsup (fun n => (P n : Measure X) (thickening δ K)) atTop := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine (iInf_le _ k).trans ?_
  exact limsup_le_limsup (Eventually.of_forall fun _ =>
    measure_mono (thickening_mono hk.le K)) (by isBoundedDefault) (by isBoundedDefault)

variable {P}

lemma aux_limit_kernel_path_limit_lam_le_add_eventually
    (hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η)
    (K : Set X) {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, aux_limit_kernel_path_limit_lam P K ≤ (P n : Measure X) (thickening δ K) + ENNReal.ofReal η := by
  set η' := min η (δ / 2) with hη'
  have hη'pos : 0 < η' := lt_min hη (half_pos hδ)
  obtain ⟨N, hN⟩ := hC η' hη'pos
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (aux_limit_kernel_path_limit_lam_le_limsup P K (half_pos hδ)).trans ?_
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop N] with m hm
  have h1 := aux_limit_kernel_path_limit_lp_le (hN m hm n hn) (isOpen_thickening (δ := δ / 2) (E := K)).measurableSet
  refine h1.trans (add_le_add ?_ (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  refine measure_mono ((thickening_thickening_subset _ _ _).trans (thickening_mono ?_ _))
  have : η' ≤ δ / 2 := min_le_right _ _
  linarith

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma aux_limit_kernel_path_limit_limsup_add_le_nat (u v : ℕ → ℝ≥0∞) :
    limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop := by
  by_cases hu : limsup u atTop = ∞
  · rw [hu, top_add]; exact le_top
  by_cases hv : limsup v atTop = ∞
  · rw [hv, add_top]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 :=
    ENNReal.div_pos (by exact_mod_cast hε.ne') ENNReal.ofNat_ne_top
  have h1 : ∀ᶠ n in atTop, u n < limsup u atTop + (ε : ℝ≥0∞) / 2 :=
    eventually_lt_of_limsup_lt (ENNReal.lt_add_right hu hε2.ne') (by isBoundedDefault)
  have h2 : ∀ᶠ n in atTop, v n < limsup v atTop + (ε : ℝ≥0∞) / 2 :=
    eventually_lt_of_limsup_lt (ENNReal.lt_add_right hv hε2.ne') (by isBoundedDefault)
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [h1, h2] with n hn1 hn2
  calc (u + v) n = u n + v n := rfl
    _ ≤ (limsup u atTop + (ε : ℝ≥0∞) / 2) + (limsup v atTop + (ε : ℝ≥0∞) / 2) :=
        add_le_add hn1.le hn2.le
    _ = limsup u atTop + limsup v atTop + ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) := by ring
    _ = limsup u atTop + limsup v atTop + ε := by rw [ENNReal.add_halves]

omit [BorelSpace X] in
lemma aux_limit_kernel_path_limit_lam_union_le (K₁ K₂ : Set X) : aux_limit_kernel_path_limit_lam P (K₁ ∪ K₂) ≤ aux_limit_kernel_path_limit_lam P K₁ + aux_limit_kernel_path_limit_lam P K₂ := by
  have hanti : ∀ (K : Set X) (i j : ℕ), i ≤ j →
      limsup (fun n => (P n : Measure X) (thickening (1 / ((j : ℝ) + 1)) K)) atTop ≤
        limsup (fun n => (P n : Measure X) (thickening (1 / ((i : ℝ) + 1)) K)) atTop := by
    intro K i j hij
    refine limsup_le_limsup (Eventually.of_forall fun _ => measure_mono (thickening_mono ?_ K))
      (by isBoundedDefault) (by isBoundedDefault)
    gcongr
  unfold aux_limit_kernel_path_limit_lam
  rw [ENNReal.iInf_add_iInf (fun i j => ⟨max i j, add_le_add
    (hanti _ _ _ (le_max_left _ _)) (hanti _ _ _ (le_max_right _ _))⟩)]
  refine iInf_mono fun k => ?_
  refine le_trans ?_ (aux_limit_kernel_path_limit_limsup_add_le_nat _ _)
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
    (by isBoundedDefault) (by isBoundedDefault)
  simp only [thickening_union, Pi.add_apply]
  exact measure_union_le _ _

lemma aux_limit_kernel_path_limit_le_lam_union
    (hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η)
    {K₁ K₂ : Set X} (hK₁ : IsCompact K₁) (hK₂ : IsClosed K₂) (hd : Disjoint K₁ K₂) :
    aux_limit_kernel_path_limit_lam P K₁ + aux_limit_kernel_path_limit_lam P K₂ ≤ aux_limit_kernel_path_limit_lam P (K₁ ∪ K₂) := by
  obtain ⟨δ₀, hδ₀, hdisj⟩ := hd.exists_thickenings hK₁ hK₂
  refine le_iInf fun k => ?_
  set δ := min (1 / ((k : ℝ) + 1)) δ₀ with hδdef
  have hδ : 0 < δ := lt_min (by positivity) hδ₀
  refine le_trans ?_ (limsup_le_limsup (Eventually.of_forall fun n =>
    measure_mono (thickening_mono (min_le_left _ δ₀) (K₁ ∪ K₂)))
    (by isBoundedDefault) (by isBoundedDefault))
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
  have hdisj' : Disjoint (thickening δ K₁) (thickening δ K₂) :=
    hdisj.mono (thickening_mono (min_le_right _ _) _) (thickening_mono (min_le_right _ _) _)
  rw [← tsub_le_iff_right]
  refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
  refine Eventually.frequently ?_
  filter_upwards [aux_limit_kernel_path_limit_lam_le_add_eventually hC K₁ hδ hε2, aux_limit_kernel_path_limit_lam_le_add_eventually hC K₂ hδ hε2]
    with n h1 h2
  rw [tsub_le_iff_right, thickening_union,
    measure_union hdisj' (isOpen_thickening (δ := δ) (E := K₂)).measurableSet]
  calc aux_limit_kernel_path_limit_lam P K₁ + aux_limit_kernel_path_limit_lam P K₂
      ≤ ((P n : Measure X) (thickening δ K₁) + ENNReal.ofReal ((ε : ℝ) / 2)) +
        ((P n : Measure X) (thickening δ K₂) + ENNReal.ofReal ((ε : ℝ) / 2)) :=
        add_le_add h1 h2
    _ = (P n : Measure X) (thickening δ K₁) + (P n : Measure X) (thickening δ K₂) +
        (ENNReal.ofReal ((ε : ℝ) / 2) + ENNReal.ofReal ((ε : ℝ) / 2)) := by ring
    _ = (P n : Measure X) (thickening δ K₁) + (P n : Measure X) (thickening δ K₂) + ε := by
        rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves, ENNReal.ofReal_coe_nnreal]

lemma aux_limit_kernel_path_limit_lam_le_liminf_open
    (hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η)
    {K G : Set X} (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G) :
    aux_limit_kernel_path_limit_lam P K ≤ liminf (fun n => (P n : Measure X) G) atTop := by
  obtain ⟨δ, hδ, hδG⟩ := hK.exists_thickening_subset_open hG hKG
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [← tsub_le_iff_right]
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [aux_limit_kernel_path_limit_lam_le_add_eventually hC K hδ (show (0 : ℝ) < ε by exact_mod_cast hε)]
    with n hn
  rw [tsub_le_iff_right]
  refine hn.trans (add_le_add (measure_mono hδG) ?_)
  rw [ENNReal.ofReal_coe_nnreal]

lemma aux_limit_kernel_path_limit_finite_tight [CompleteSpace X] [SecondCountableTopology X]
    {η : ℝ} (hη : 0 < η) (N : ℕ) :
    ∃ C : Set X, IsCompact C ∧ ∀ m ≤ N, (P m : Measure X) Cᶜ ≤ ENNReal.ofReal η := by
  have hsingle : ∀ m, ∃ C : Set X, IsCompact C ∧ (P m : Measure X) Cᶜ ≤ ENNReal.ofReal η := by
    intro m
    have ht := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le
      (S := {(P m : Measure X)})).1 isTightMeasureSet_singleton (ENNReal.ofReal η)
      (ENNReal.ofReal_pos.2 hη)
    obtain ⟨C, hC, hCm⟩ := ht
    exact ⟨C, hC, hCm _ rfl⟩
  choose C hCc hCm using hsingle
  refine ⟨⋃ m ∈ Finset.range (N + 1), C m,
    (Finset.range (N + 1)).isCompact_biUnion fun m _ => hCc m, fun m hm => ?_⟩
  refine le_trans (measure_mono ?_) (hCm m)
  refine compl_subset_compl.2 ?_
  exact subset_biUnion_of_mem (u := C) (Finset.mem_coe.2 (Finset.mem_range.2 (by omega)))

omit [MeasurableSpace X] [BorelSpace X] in
lemma aux_limit_kernel_path_limit_thickening_compl_thickening_subset (η : ℝ) (C : Set X) :
    thickening η (thickening η C)ᶜ ⊆ Cᶜ := by
  intro y hy hyC
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
  exact hz (mem_thickening_iff.2 ⟨y, hyC, by rwa [dist_comm]⟩)

lemma aux_limit_kernel_path_limit_tight [CompleteSpace X] [SecondCountableTopology X]
    (hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ ∀ n, (P n : Measure X) Kᶜ ≤ ENNReal.ofReal ε := by
  set θ : ℕ → ℝ := fun j => ε / 2 / 2 ^ j with hθ
  have hθpos : ∀ j, 0 < θ j := fun j => by positivity
  set η : ℕ → ℝ := fun j => θ j / 2 with hηdef
  have hηpos : ∀ j, 0 < η j := fun j => half_pos (hθpos j)
  choose N hN using fun j => hC (η j) (hηpos j)
  choose C hCc hCm using fun j => aux_limit_kernel_path_limit_finite_tight (P := P) (hηpos j) (N j)
  have hbound : ∀ j n, (P n : Measure X) (thickening (η j) (C j))ᶜ ≤ ENNReal.ofReal (θ j) := by
    intro j n
    have hsplit : ENNReal.ofReal (θ j) = ENNReal.ofReal (η j) + ENNReal.ofReal (η j) := by
      rw [← ENNReal.ofReal_add (hηpos j).le (hηpos j).le, hηdef, add_halves]
    rcases le_total n (N j) with hn | hn
    · refine (measure_mono (compl_subset_compl.2 (self_subset_thickening (hηpos j) _))).trans ?_
      refine (hCm j n hn).trans ?_
      rw [hsplit]
      exact le_add_self
    · have h1 := aux_limit_kernel_path_limit_lp_le (hN j n hn (N j) le_rfl)
        (isOpen_thickening (δ := η j) (E := C j)).isClosed_compl.measurableSet
      refine h1.trans ?_
      rw [hsplit]
      refine add_le_add ?_ le_rfl
      exact (measure_mono (aux_limit_kernel_path_limit_thickening_compl_thickening_subset _ _)).trans (hCm j (N j) le_rfl)
  refine ⟨⋂ j, cthickening (η j) (C j), ?_, fun n => ?_⟩
  · refine TotallyBounded.isCompact_of_isClosed ?_ (isClosed_iInter fun j => isClosed_cthickening)
    rw [Metric.totallyBounded_iff]
    intro r hr
    have hlim : Tendsto η atTop (𝓝 0) := by
      have : Tendsto (fun j : ℕ => ε / 2 / 2 * ((1 : ℝ) / 2) ^ j) atTop (𝓝 (ε / 2 / 2 * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
      rw [mul_zero] at this
      refine this.congr fun j => ?_
      simp only [hηdef, hθ]
      rw [one_div_pow]
      field_simp
    obtain ⟨j, hj⟩ := ((hlim.eventually (gt_mem_nhds (half_pos hr))).and
      (Eventually.of_forall fun j => hηpos j)).exists
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 (hCc j).totallyBounded (r / 2)
      (half_pos hr)
    refine ⟨t, ht, fun x hx => ?_⟩
    have hx' : x ∈ thickening (r / 2) (C j) :=
      cthickening_subset_thickening' (half_pos hr) hj.1 _ (mem_iInter.1 hx j)
    obtain ⟨c, hc, hxc⟩ := mem_thickening_iff.1 hx'
    obtain ⟨y, hy, hcy⟩ := mem_iUnion₂.1 (hcover hc)
    refine mem_iUnion₂.2 ⟨y, hy, ?_⟩
    rw [mem_ball] at hcy ⊢
    calc dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hxc hcy
      _ = r := add_halves r
  · rw [compl_iInter]
    refine (measure_iUnion_le _).trans ?_
    calc ∑' j, (P n : Measure X) (cthickening (η j) (C j))ᶜ
        ≤ ∑' j, ENNReal.ofReal (θ j) := ENNReal.tsum_le_tsum fun j =>
          (measure_mono (compl_subset_compl.2 (thickening_subset_cthickening _ _))).trans (hbound j n)
      _ = ENNReal.ofReal (∑' j, θ j) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => (hθpos j).le)
            (by simpa [hθ] using (summable_geometric_two' ε))).symm
      _ = ENNReal.ofReal ε := by rw [hθ, tsum_geometric_two']

variable (P) in
/-- The content of a Lévy–Prokhorov Cauchy sequence. -/
def aux_limit_kernel_path_limit_lamContent
    (hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η) :
    MeasureTheory.Content X where
  toFun K := (aux_limit_kernel_path_limit_lam P K).toNNReal
  mono' K₁ K₂ h := ENNReal.toNNReal_mono (aux_limit_kernel_path_limit_lam_ne_top P _) (aux_limit_kernel_path_limit_lam_mono P h)
  sup_disjoint' K₁ K₂ hd _ h₂ := by
    rw [← ENNReal.toNNReal_add (aux_limit_kernel_path_limit_lam_ne_top P _) (aux_limit_kernel_path_limit_lam_ne_top P _)]
    congr 1
    exact le_antisymm (aux_limit_kernel_path_limit_lam_union_le _ _) (aux_limit_kernel_path_limit_le_lam_union hC K₁.isCompact h₂ hd)
  sup_le' K₁ K₂ := by
    rw [← ENNReal.toNNReal_add (aux_limit_kernel_path_limit_lam_ne_top P _) (aux_limit_kernel_path_limit_lam_ne_top P _)]
    exact ENNReal.toNNReal_mono (ENNReal.add_ne_top.2 ⟨aux_limit_kernel_path_limit_lam_ne_top P _, aux_limit_kernel_path_limit_lam_ne_top P _⟩)
      (aux_limit_kernel_path_limit_lam_union_le _ _)

lemma aux_limit_kernel_path_limit_lamContent_apply
    (hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η)
    (K : TopologicalSpace.Compacts X) : aux_limit_kernel_path_limit_lamContent P hC K = aux_limit_kernel_path_limit_lam P K := by
  change ((aux_limit_kernel_path_limit_lam P K).toNNReal : ℝ≥0∞) = aux_limit_kernel_path_limit_lam P K
  exact ENNReal.coe_toNNReal (aux_limit_kernel_path_limit_lam_ne_top P _)

lemma aux_limit_kernel_path_limit_lamMeasure_open
    (hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η)
    {G : Set X} (hG : IsOpen G) :
    (aux_limit_kernel_path_limit_lamContent P hC).measure G =
      ⨆ (K : TopologicalSpace.Compacts X) (_ : (K : Set X) ⊆ G), aux_limit_kernel_path_limit_lam P K := by
  rw [MeasureTheory.Content.measure_apply _ hG.measurableSet,
    MeasureTheory.Content.outerMeasure_of_isOpen _ _ hG]
  simp only [MeasureTheory.Content.innerContent, aux_limit_kernel_path_limit_lamContent_apply]
  rfl

lemma aux_limit_kernel_path_limit_lamMeasure_univ [CompleteSpace X] [SecondCountableTopology X]
    (hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η) :
    (aux_limit_kernel_path_limit_lamContent P hC).measure univ = 1 := by
  rw [aux_limit_kernel_path_limit_lamMeasure_open hC isOpen_univ]
  refine le_antisymm (iSup₂_le fun K _ => aux_limit_kernel_path_limit_lam_le_one P K) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨K, hK, hKn⟩ := aux_limit_kernel_path_limit_tight hC (show (0 : ℝ) < ε by exact_mod_cast hε)
  refine le_trans ?_ (add_le_add (le_iSup₂ (f := fun (K : TopologicalSpace.Compacts X) _ =>
    aux_limit_kernel_path_limit_lam P K) ⟨K, hK⟩ (subset_univ _)) le_rfl)
  rw [← tsub_le_iff_right]
  refine le_iInf fun k => le_limsup_of_frequently_le (Eventually.frequently
    (Eventually.of_forall fun n => ?_)) (by isBoundedDefault)
  refine le_trans ?_ (measure_mono (self_subset_thickening (by positivity) K))
  rw [tsub_le_iff_right]
  have := hKn n
  rw [prob_compl_eq_one_sub hK.isClosed.measurableSet, ENNReal.ofReal_coe_nnreal] at this
  calc (1 : ℝ≥0∞) ≤ (P n : Measure X) K + (1 - (P n : Measure X) K) := le_add_tsub
    _ ≤ (P n : Measure X) K + ε := add_le_add le_rfl this

theorem aux_limit_kernel_path_limit_exists_tendsto_of_cauchy [CompleteSpace X] [SecondCountableTopology X]
    (hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η) :
    ∃ Q : ProbabilityMeasure X, Tendsto P atTop (𝓝 Q) := by
  have : IsProbabilityMeasure (aux_limit_kernel_path_limit_lamContent P hC).measure := ⟨aux_limit_kernel_path_limit_lamMeasure_univ hC⟩
  refine ⟨⟨(aux_limit_kernel_path_limit_lamContent P hC).measure, inferInstance⟩, ?_⟩
  refine tendsto_of_forall_isOpen_le_liminf_nat' fun G hG => ?_
  change (aux_limit_kernel_path_limit_lamContent P hC).measure G ≤ _
  rw [aux_limit_kernel_path_limit_lamMeasure_open hC hG]
  exact iSup₂_le fun K hK => aux_limit_kernel_path_limit_lam_le_liminf_open hC K.isCompact hG hK

theorem aux_limit_kernel_path_limit_completeSpace [CompleteSpace X] [SecondCountableTopology X] :
    CompleteSpace (LevyProkhorov (ProbabilityMeasure X)) := by
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  set P : ℕ → ProbabilityMeasure X := fun n => (u n).toMeasure
  have hC : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      dist (LevyProkhorov.ofMeasure (P n)) (LevyProkhorov.ofMeasure (P m)) < η :=
    Metric.cauchySeq_iff.1 hu
  obtain ⟨Q, hQ⟩ := aux_limit_kernel_path_limit_exists_tendsto_of_cauchy hC
  exact ⟨LevyProkhorov.ofMeasure Q,
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto Q).comp hQ⟩


lemma aux_limit_kernel_path_limit_geom_tail {Y : Type*} [PseudoMetricSpace Y] {u : ℕ → Y} {a : Y} {k : ℕ}
    (hu : ∀ i ≥ k, dist (u i) (u (i + 1)) < (1 / 2 : ℝ) ^ i)
    (ha : Tendsto u atTop (𝓝 a)) : dist (u k) a ≤ 2 * (1 / 2 : ℝ) ^ k := by
  have hv : ∀ j, dist (u (j + k)) (u (j + 1 + k)) ≤ (2 * (1 / 2 : ℝ) ^ k) / 2 / 2 ^ j := by
    intro j
    rw [show j + 1 + k = j + k + 1 by omega]
    refine (hu (j + k) (Nat.le_add_left _ _)).le.trans (le_of_eq ?_)
    rw [pow_add]
    field_simp
    rw [← mul_pow]; norm_num
  have := dist_le_of_le_geometric_two_of_tendsto hv ((tendsto_add_atTop_iff_nat k).2 ha) 0
  simpa using this

lemma aux_limit_kernel_path_limit_geom_exists {Y : Type*} [PseudoMetricSpace Y] [CompleteSpace Y] {u : ℕ → Y} {k : ℕ}
    (hu : ∀ i ≥ k, dist (u i) (u (i + 1)) < (1 / 2 : ℝ) ^ i) :
    ∃ a, Tendsto u atTop (𝓝 a) := by
  have hv : ∀ j, dist (u (j + k)) (u (j + 1 + k)) ≤ 2 / 2 / 2 ^ j := by
    intro j
    rw [show j + 1 + k = j + k + 1 by omega]
    refine (hu (j + k) (Nat.le_add_left _ _)).le.trans ?_
    rw [show (2 : ℝ) / 2 / 2 ^ j = (1 / 2) ^ j by field_simp; rw [← mul_pow]; norm_num]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ _)
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hv)
  exact ⟨a, (tendsto_add_atTop_iff_nat k).1 ha⟩

lemma aux_limit_kernel_path_limit_exists_two_mul_half_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, 2 * (1 / 2 : ℝ) ^ k < ε := by
  have : Tendsto (fun k : ℕ => 2 * (1 / 2 : ℝ) ^ k) atTop (𝓝 (2 * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 2
  rw [mul_zero] at this
  exact (this.eventually (gt_mem_nhds hε)).exists

lemma aux_limit_kernel_path_limit_two_mul_half_pow_anti {k k' : ℕ} (h : k' ≤ k) :
    2 * (1 / 2 : ℝ) ^ k ≤ 2 * (1 / 2 : ℝ) ^ k' :=
  mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) (by norm_num)

theorem aux_limit_kernel_path_limit_reduction [CompleteSpace X] [SecondCountableTopology X]
    {Ω S : Type*} [MeasurableSpace Ω] [MetricSpace S] [ProperSpace S] [MeasurableSpace S]
    [Nonempty S] {μ : Measure Ω}
    (F : ℕ → Ω → S → ProbabilityMeasure X)
    (hF : ∀ N, Measurable (fun p : Ω × S => F N p.1 p.2))
    (hcauchy : ∀ B : Set S, IsCompact B → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
        μ {ω | ∃ x ∈ B, eps ≤ dist (LevyProkhorov.ofMeasure (F N ω x))
          (LevyProkhorov.ofMeasure (F N' ω x))} ≤ ENNReal.ofReal rho)
    (hcont : ∀ᵐ ω ∂μ, ∀ N, Continuous (F N ω)) :
    ∃ L : Ω → S → ProbabilityMeasure X,
      Measurable (fun p : Ω × S => L p.1 p.2) ∧ (∀ᵐ ω ∂μ, Continuous (L ω)) ∧
      ∀ B : Set S, IsCompact B → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
          μ {ω | ∃ x ∈ B, eps ≤ dist (LevyProkhorov.ofMeasure (F N ω x))
            (LevyProkhorov.ofMeasure (L ω x))} ≤ ENNReal.ofReal rho := by
  classical
  have : CompleteSpace (LevyProkhorov (ProbabilityMeasure X)) := aux_limit_kernel_path_limit_completeSpace
  obtain ⟨x0⟩ := ‹Nonempty S›
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Ω → S → LevyProkhorov (ProbabilityMeasure X),
      ∀ N ω x, D N ω x = LevyProkhorov.ofMeasure (F N ω x) := ⟨_, fun _ _ _ => rfl⟩
  simp_rw [← hD] at hcauchy
  simp_rw [← hD]
  have hDcont : ∀ ω N, Continuous (F N ω) → Continuous (D N ω) := by
    intro ω N h
    have : D N ω = fun x => LevyProkhorov.ofMeasure (F N ω x) := funext fun x => hD N ω x
    rw [this]
    exact LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp h
  -- A fast subsequence.
  have hstep : ∀ k : ℕ, ∃ M : ℕ, ∀ N N' : ℕ, M ≤ N → M ≤ N' →
      μ {ω | ∃ x ∈ closedBall x0 k, (1 / 2 : ℝ) ^ k ≤ dist (D N ω x) (D N' ω x)} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
    fun k => hcauchy _ (isCompact_closedBall x0 k) _ (by positivity) _ (by positivity)
  choose M hM using hstep
  obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ, ∀ k, n k = (Finset.range (k + 1)).sup M + k := ⟨_, fun _ => rfl⟩
  have hn_mono : Monotone n := by
    intro a b hab
    rw [hn, hn]
    exact add_le_add (Finset.sup_mono (Finset.range_subset_range.2 (by omega))) hab
  have hn_ge : ∀ k, M k ≤ n k := fun k => by
    rw [hn]
    exact le_trans (Finset.le_sup (f := M) (Finset.mem_range.2 (Nat.lt_succ_self k)))
      (Nat.le_add_right _ _)
  have hn_ge' : ∀ k, k ≤ n k := fun k => by rw [hn]; exact Nat.le_add_left _ _
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set Ω, ∀ k, E k = {ω | ∃ x ∈ closedBall x0 k,
      (1 / 2 : ℝ) ^ k ≤ dist (D (n k) ω x) (D (n (k + 1)) ω x)} := ⟨_, fun _ => rfl⟩
  have hEμ : ∀ k, μ (E k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := fun k => by
    rw [hE]
    exact hM k _ _ (hn_ge k) ((hn_ge k).trans (hn_mono (Nat.le_succ k)))
  have hsum : ∑' k, μ (E k) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2)) ?_
    calc ∑' k, μ (E k) ≤ ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := ENNReal.tsum_le_tsum hEμ
      _ = ENNReal.ofReal (∑' k, (1 / 2 : ℝ) ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_geometric_two).symm
      _ = ENNReal.ofReal 2 := by rw [tsum_geometric_two]
  have htail : ∀ k, μ (⋃ i, E (i + k)) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
    intro k
    refine (measure_iUnion_le _).trans ?_
    have hs : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + k)) :=
      (summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ k)).congr fun i => (pow_add _ _ _).symm
    calc ∑' i, μ (E (i + k)) ≤ ∑' i, ENNReal.ofReal ((1 / 2 : ℝ) ^ (i + k)) :=
          ENNReal.tsum_le_tsum fun i => hEμ _
      _ = ENNReal.ofReal (∑' i, (1 / 2 : ℝ) ^ (i + k)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs).symm
      _ = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
          congr 1
          simp_rw [pow_add]
          rw [tsum_mul_right, tsum_geometric_two]
  have hlimsup : μ (limsup E atTop) = 0 := measure_limsup_atTop_eq_zero hsum
  -- The good event.
  set Bad : Set Ω := limsup E atTop ∪ {ω | ¬ ∀ N, Continuous (F N ω)} with hBad_def
  have hBad : μ Bad = 0 := measure_union_null hlimsup (ae_iff.1 hcont)
  set G0 : Set Ω := (toMeasurable μ Bad)ᶜ with hG0_def
  have hG0 : MeasurableSet G0 := (measurableSet_toMeasurable μ Bad).compl
  have hG0c : μ G0ᶜ = 0 := by rw [hG0_def, compl_compl, measure_toMeasurable, hBad]
  have hG0ae : ∀ᵐ ω ∂μ, ω ∈ G0 := ae_iff.2 hG0c
  have hG0good : ∀ ω ∈ G0, ω ∉ Bad := fun ω hω hb => hω (subset_toMeasurable μ Bad hb)
  have hG0E : ∀ ω ∈ G0, ∃ k0, ∀ k ≥ k0, ω ∉ E k := by
    intro ω hω
    have h : ω ∉ limsup E atTop := fun h => hG0good ω hω (Or.inl h)
    rw [mem_limsup_iff_frequently_mem, not_frequently] at h
    exact eventually_atTop.1 h
  have hG0cont : ∀ ω ∈ G0, ∀ N, Continuous (F N ω) := fun ω hω => by
    by_contra h
    exact hG0good ω hω (Or.inr h)
  have hgeom : ∀ ω x k, (∀ i ≥ k, ω ∉ E i) → dist x x0 ≤ k →
      ∀ i ≥ k, dist (D (n i) ω x) (D (n (i + 1)) ω x) < (1 / 2 : ℝ) ^ i := by
    intro ω x k hk hx i hi
    by_contra hcon
    push Not at hcon
    refine hk i hi ?_
    rw [hE]
    exact ⟨x, mem_closedBall.2 (hx.trans (by exact_mod_cast hi)), hcon⟩
  have hexists : ∀ ω ∈ G0, ∀ x, ∃ a, Tendsto (fun k => D (n k) ω x) atTop (𝓝 a) := by
    intro ω hω x
    obtain ⟨k0, hk0⟩ := hG0E ω hω
    obtain ⟨j, hj⟩ := exists_nat_ge (dist x x0)
    exact aux_limit_kernel_path_limit_geom_exists (k := max k0 j) (hgeom ω x (max k0 j)
      (fun i hi => hk0 i (le_trans (le_max_left _ _) hi))
      (hj.trans (by exact_mod_cast le_max_right _ _)))
  obtain ⟨Lim, hLim_def⟩ : ∃ Lim : Ω → S → LevyProkhorov (ProbabilityMeasure X),
      ∀ ω x, Lim ω x = @limUnder _ _ _ ⟨D 0 ω x⟩ atTop (fun k => D (n k) ω x) :=
    ⟨_, fun _ _ => rfl⟩
  have hLim : ∀ ω ∈ G0, ∀ x, Tendsto (fun k => D (n k) ω x) atTop (𝓝 (Lim ω x)) :=
    fun ω hω x => by rw [hLim_def]; exact tendsto_nhds_limUnder (hexists ω hω x)
  obtain ⟨L, hL⟩ : ∃ L : Ω → S → ProbabilityMeasure X, ∀ ω x,
      L ω x = if ω ∈ G0 then (Lim ω x).toMeasure else F 0 ω x := ⟨_, fun _ _ => rfl⟩
  have hLG : ∀ ω ∈ G0, ∀ x, LevyProkhorov.ofMeasure (L ω x) = Lim ω x := by
    intro ω hω x
    rw [hL, ite_eq_left hω]
  have hunif : ∀ ω x k, ω ∈ G0 → (∀ i ≥ k, ω ∉ E i) → dist x x0 ≤ k →
      dist (D (n k) ω x) (Lim ω x) ≤ 2 * (1 / 2 : ℝ) ^ k :=
    fun ω x k hω hk hx => aux_limit_kernel_path_limit_geom_tail (hgeom ω x k hk hx) (hLim ω hω x)
  have hweak : ∀ ω ∈ G0, ∀ x, Tendsto (fun k => F (n k) ω x) atTop (𝓝 (L ω x)) := by
    intro ω hω x
    have h := (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto (Lim ω x)).comp
      (hLim ω hω x)
    rw [hL, ite_eq_left hω]
    refine h.congr fun k => ?_
    simp [Function.comp, hD]
  refine ⟨L, ?_, ?_, ?_⟩
  · -- Measurability through bounded continuous test functions and closed sets.
    have hlint : ∀ f : X →ᵇ ℝ≥0, Measurable (fun p : Ω × S =>
        ∫⁻ y, (f y : ℝ≥0∞) ∂(L p.1 p.2 : Measure X)) := by
      intro f
      have hfm : Measurable (fun y => (f y : ℝ≥0∞)) :=
        (ENNReal.continuous_coe.comp f.continuous).measurable
      have hFm : ∀ N, Measurable (fun p : Ω × S =>
          ∫⁻ y, (f y : ℝ≥0∞) ∂(F N p.1 p.2 : Measure X)) :=
        fun N => (Measure.measurable_lintegral hfm).comp (measurable_subtype_coe.comp (hF N))
      refine measurable_of_tendsto_metrizable (f := fun k (p : Ω × S) =>
        if p.1 ∈ G0 then ∫⁻ y, (f y : ℝ≥0∞) ∂(F (n k) p.1 p.2 : Measure X)
        else ∫⁻ y, (f y : ℝ≥0∞) ∂(F 0 p.1 p.2 : Measure X))
        (fun k => Measurable.ite (measurable_fst hG0) (hFm _) (hFm _)) ?_
      rw [tendsto_pi_nhds]
      intro p
      by_cases hp : p.1 ∈ G0
      · simp only [hp, ite_true]
        exact ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 (hweak p.1 hp p.2) f
      · simp only [hp, ite_false, hL]
        exact tendsto_const_nhds
    have hclosed : ∀ C : Set X, IsClosed C →
        Measurable (fun p : Ω × S => (L p.1 p.2 : Measure X) C) := by
      intro C hC
      have hδ : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => by positivity
      refine measurable_of_tendsto_metrizable (fun m => hlint (thickenedIndicator (hδ m) C)) ?_
      rw [tendsto_pi_nhds]
      intro p
      exact tendsto_lintegral_thickenedIndicator_of_isClosed (L p.1 p.2 : Measure X) hC hδ
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hmeas : Measurable (fun p : Ω × S => (L p.1 p.2 : Measure X)) := by
      refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure (S := {C | IsClosed C})
        ?_ isPiSystem_isClosed (fun C hC => hclosed C hC)
      rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]
    exact hmeas.subtype_mk
  · filter_upwards [hG0ae] with ω hω
    obtain ⟨k0, hk0⟩ := hG0E ω hω
    have hLω : L ω = fun x => LevyProkhorov.toMeasure (Lim ω x) := by
      funext x
      rw [hL, ite_eq_left hω]
    rw [hLω]
    refine LevyProkhorov.continuous_toMeasure_probabilityMeasure.comp ?_
    refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨j, hj⟩ := exists_nat_gt (dist x x0)
    have hU : TendstoUniformlyOn (fun k y => D (n k) ω y) (Lim ω) atTop (ball x0 j) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨k1, hk1⟩ := aux_limit_kernel_path_limit_exists_two_mul_half_pow_lt hε
      filter_upwards [eventually_ge_atTop (max (max k0 j) k1)] with k hk y hy
      rw [dist_comm]
      refine lt_of_le_of_lt (hunif ω y k hω (fun i hi => hk0 i (by omega)) ?_) ?_
      · exact (mem_ball.1 hy).le.trans (by exact_mod_cast (show j ≤ k by omega))
      · exact lt_of_le_of_lt (aux_limit_kernel_path_limit_two_mul_half_pow_anti (show k1 ≤ k by omega)) hk1
    exact (hU.continuousOn (Eventually.of_forall fun k =>
      (hDcont ω (n k) (hG0cont ω hω (n k))).continuousOn).frequently).continuousAt
        (isOpen_ball.mem_nhds (mem_ball.2 hj))
  · intro B hB eps heps rho hrho
    obtain ⟨R, hR⟩ : ∃ R : ℕ, B ⊆ closedBall x0 R := by
      obtain ⟨r, hr⟩ := hB.isBounded.subset_closedBall x0
      obtain ⟨R, hR⟩ := exists_nat_ge r
      exact ⟨R, hr.trans (closedBall_subset_closedBall hR)⟩
    obtain ⟨N1, hN1⟩ := hcauchy B hB (eps / 2) (half_pos heps) (rho / 2) (half_pos hrho)
    obtain ⟨k1, hk1⟩ := aux_limit_kernel_path_limit_exists_two_mul_half_pow_lt (lt_min (half_pos heps) (half_pos hrho))
    set k := max (max R N1) k1 with hk_def
    have hk2 : 2 * (1 / 2 : ℝ) ^ k < min (eps / 2) (rho / 2) :=
      lt_of_le_of_lt (aux_limit_kernel_path_limit_two_mul_half_pow_anti (show k1 ≤ k by omega)) hk1
    refine ⟨N1, fun N hN => ?_⟩
    have hsub : {ω | ∃ x ∈ B, eps ≤ dist (D N ω x) (LevyProkhorov.ofMeasure (L ω x))} ⊆
        {ω | ∃ x ∈ B, eps / 2 ≤ dist (D N ω x) (D (n k) ω x)} ∪ (G0ᶜ ∪ ⋃ i, E (i + k)) := by
      rintro ω ⟨x, hxB, hx⟩
      by_cases hω : ω ∈ G0
      · by_cases hEk : ω ∈ ⋃ i, E (i + k)
        · exact Or.inr (Or.inr hEk)
        · left
          refine ⟨x, hxB, ?_⟩
          have hk' : ∀ i ≥ k, ω ∉ E i := fun i hi hEi =>
            hEk (mem_iUnion.2 ⟨i - k, by rwa [Nat.sub_add_cancel hi]⟩)
          have hxk : dist x x0 ≤ k :=
            (mem_closedBall.1 (hR hxB)).trans (by exact_mod_cast (show R ≤ k by omega))
          have h1 := hunif ω x k hω hk' hxk
          rw [hLG ω hω x] at hx
          have h2 := dist_triangle (D N ω x) (D (n k) ω x) (Lim ω x)
          have h3 : 2 * (1 / 2 : ℝ) ^ k < eps / 2 := lt_of_lt_of_le hk2 (min_le_left _ _)
          linarith
      · exact Or.inr (Or.inl hω)
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (hN1 N (n k) hN (le_trans (by omega) (hn_ge' k)))
      ((measure_union_le _ _).trans (add_le_add (le_of_eq hG0c) (htail k)))).trans ?_
    rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h4 : 2 * (1 / 2 : ℝ) ^ k < rho / 2 := lt_of_lt_of_le hk2 (min_le_right _ _)
    linarith


end PathLawLimitGeneric


/- The one analytic construction not exported by the imported path-law API is
   isolated here: a compact-start, probability-valued Cauchy family has a
   jointly measurable version of its limit, with the a.e. continuous and full
   locally-uniform-in-probability conclusions.  The wrapper below is then just
   the genuine kernel construction from that probability-valued map. -/
theorem aux_limit_kernel_path_limit_compact_measurable_version
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {μ : Measure (BilateralField d)} [IsProbabilityMeasure μ]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hcauchy : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
          μ
              {omega : BilateralField d | ∃ x ∈ B, eps ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                  (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
            ENNReal.ofReal rho)
    (hcont : ∀ᵐ omega ∂μ,
      ∀ N : ℕ, Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x)) :
    ∃ L : BilateralField d → SpatialCoordinates d →
        ProbabilityMeasure (DiffusionPath d),
      Measurable (fun p : BilateralField d × SpatialCoordinates d =>
        L p.1 p.2) ∧
      (∀ᵐ omega ∂μ, Continuous (L omega)) ∧
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
            μ
                {omega : BilateralField d | ∃ x ∈ B, eps ≤
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (L omega x)} ≤
              ENNReal.ofReal rho := by
  let : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  have : @CompleteSpace (DiffusionPath d) PseudoMetricSpace.toUniformSpace :=
    TopologicalSpace.complete_completelyMetrizableMetric (DiffusionPath d)
  exact aux_limit_kernel_path_limit_reduction
    (fun N omega x => jointPathProbabilityMeasure (KN N) (hKN N) omega x)
    (fun N => (KN N).measurable.subtype_mk) hcauchy hcont

theorem aux_limit_kernel_path_limit_kernel_of_measurable_limit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (L : BilateralField d → SpatialCoordinates d →
      ProbabilityMeasure (DiffusionPath d))
    (hL : Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      L p.1 p.2)) :
    ∃ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
      (hK : IsMarkovKernel K),
      ∀ (omega : BilateralField d) (x : SpatialCoordinates d),
        jointPathProbabilityMeasure K hK omega x = L omega x := by
  let K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d) :=
    { toFun := fun p => (L p.1 p.2 : Measure (DiffusionPath d))
      measurable' := hL.subtype_val }
  have hK : IsMarkovKernel K := by
    refine ⟨fun p => ?_⟩
    exact (L p.1 p.2).prop
  refine ⟨K, hK, ?_⟩
  intro omega x
  rfl

-- Passage to the limiting path law with the displayed kernel identities.
theorem limit_kernel_path_limit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hcauchy : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
          (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                  (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
            ENNReal.ofReal rho)
    (hcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N : ℕ, Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x)) :
    ∃ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
      (hK : IsMarkovKernel K),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        Continuous (fun x : SpatialCoordinates d =>
          jointPathProbabilityMeasure K hK omega x)) ∧
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
            (chaosSampleLaw M).toMeasure
                {omega : BilateralField d | ∃ x ∈ B, eps ≤
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x)} ≤
              ENNReal.ofReal rho := by
  classical
  obtain ⟨L, hL, hLcont, hLconv⟩ :=
    aux_limit_kernel_path_limit_compact_measurable_version
      (μ := (chaosSampleLaw M).toMeasure) KN hKN hcauchy hcont
  obtain ⟨K, hK, hKL⟩ :=
    aux_limit_kernel_path_limit_kernel_of_measurable_limit L hL
  refine ⟨K, hK, ?_, ?_⟩
  · filter_upwards [hLcont] with omega hω
    rw [show (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure K hK omega x) = L omega by
      funext x
      exact hKL omega x]
    exact hω
  · intro B hB eps heps rho hrho
    obtain ⟨N0, hN0⟩ := hLconv B hB eps heps rho hrho
    refine ⟨N0, ?_⟩
    intro N hN
    convert hN0 N hN using 1
    congr 2
    ext omega
    constructor
    · rintro ⟨x, hxB, hx⟩
      exact ⟨x, hxB, by simpa [hKL omega x] using hx⟩
    · rintro ⟨x, hxB, hx⟩
      exact ⟨x, hxB, by simpa [hKL omega x] using hx⟩

end SubdiffusiveProcess.Paper
