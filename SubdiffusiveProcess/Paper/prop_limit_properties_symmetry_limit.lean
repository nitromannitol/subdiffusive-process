module

public import SubdiffusiveProcess.Paper.limit_kernel_path_limit
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import SubdiffusiveProcess.Paper.prop_limit_properties_cutoff_symmetry
public import SubdiffusiveProcess.Paper.limit_kernel
public import SubdiffusiveProcess.Paper.prop_quenched_convergence
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Paper.in_crossing

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_prop_limit_properties_symmetry_limit_sigmaFinite
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {mu : Measure (SpatialCoordinates d)} (h : IsLocallyFiniteMeasure mu) :
    SigmaFinite mu ∧ (∀ j : ℕ, mu (Metric.ball (0 : SpatialCoordinates d) (j+1)) ≠ ⊤) := by
  have hball_fin : ∀ j : ℕ, mu (Metric.ball (0 : SpatialCoordinates d) (j+1)) < ⊤ := by
    intro j
    have hU : ∀ x : SpatialCoordinates d,
        ∃ U : Set (SpatialCoordinates d), IsOpen U ∧ x ∈ U ∧ mu U < ⊤ := by
      intro x
      obtain ⟨s, hs, hsμ⟩ := h.finiteAtNhds x
      rw [mem_nhds_iff] at hs
      obtain ⟨t, hts, htopen, hxt⟩ := hs
      exact ⟨t, htopen, hxt, lt_of_le_of_lt (measure_mono hts) hsμ⟩
    choose U hUopen hxU hUμ using hU
    have hcover : Metric.closedBall (0 : SpatialCoordinates d) (j+1) ⊆ ⋃ x, U x :=
      fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩
    obtain ⟨t, ht⟩ :=
      (isCompact_closedBall (0 : SpatialCoordinates d) (j+1)).elim_finite_subcover U hUopen hcover
    have hclosed : mu (Metric.closedBall (0 : SpatialCoordinates d) (j+1)) < ⊤ := by
      calc mu (Metric.closedBall (0 : SpatialCoordinates d) (j+1))
          ≤ mu (⋃ x ∈ t, U x) := measure_mono ht
        _ ≤ ∑ x ∈ t, mu (U x) := measure_biUnion_finset_le t U
        _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ => hUμ x
    exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall) hclosed
  constructor
  · refine Measure.sigmaFinite_of_countable
      (S := Set.range (fun j : ℕ => Metric.ball (0 : SpatialCoordinates d) (j+1))) ?_ ?_ ?_
    · exact Set.countable_range _
    · rintro s ⟨j, rfl⟩
      exact hball_fin j
    · rw [Set.sUnion_range]
      exact Metric.iUnion_ball_nat_succ 0
  · intro j
    exact (hball_fin j).ne

theorem aux_prop_limit_properties_symmetry_limit_subseq
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hconv : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      Tendsto (fun N ↦ (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)}) atTop (nhds 0)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
        ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
        ∃ J : ℕ, ∀ j ≥ J, ∀ x ∈ B,
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN (φ j)) (hKN (φ j)) omega x)
            (jointPathProbabilityMeasure K hK omega x) < eps := by
  let mu : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have key : ∀ j : ℕ, ∃ N0 : ℕ, ∀ N ≥ N0,
      mu {omega : BilateralField d |
        ∃ x ∈ Metric.closedBall (0 : SpatialCoordinates d) ((j : ℝ) + 1),
          (1 : ℝ) / ((j : ℝ) + 1) ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)}
      < ((1 / 2 : ℝ≥0∞)) ^ (j + 1) := by
    intro j
    have hpos : (0 : ℝ≥0∞) < (1 / 2) ^ (j + 1) := ENNReal.pow_pos (by norm_num) _
    have hlt := (hconv (Metric.closedBall (0 : SpatialCoordinates d) ((j : ℝ) + 1))
      (ProperSpace.isCompact_closedBall (0 : SpatialCoordinates d) ((j : ℝ) + 1))
      (1 / ((j : ℝ) + 1)) (by positivity)).eventually_lt_const hpos
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hlt
    exact ⟨N0, hN0⟩
  choose Nraw hNraw using key
  let phi : ℕ → ℕ := fun j => max j (Nraw j)
  have hphi_cof : Tendsto phi atTop atTop :=
    tendsto_atTop_atTop.mpr (fun a => ⟨a, fun b hb => le_trans hb (le_max_left b (Nraw b))⟩)
  let A : ℕ → Set (BilateralField d) := fun j => {omega : BilateralField d |
      ∃ x ∈ Metric.closedBall (0 : SpatialCoordinates d) ((j : ℝ) + 1),
        (1 : ℝ) / ((j : ℝ) + 1) ≤
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN (phi j)) (hKN (phi j)) omega x)
            (jointPathProbabilityMeasure K hK omega x)}
  have hAle : ∀ j, mu (A j) < ((1 / 2 : ℝ≥0∞)) ^ (j + 1) :=
    fun j => hNraw j (phi j) (le_max_right j (Nraw j))
  have hsum : (∑' j : ℕ, mu (A j)) ≠ ∞ := by
    have hfin : (∑' j : ℕ, ((1 / 2 : ℝ≥0∞)) ^ (j + 1)) ≠ ∞ := by
      have hb : (∑' j : ℕ, ((2 : ℝ≥0∞))⁻¹ ^ j) ≠ ∞ := by
        simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
          (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ⊤)
      have key2 : (∑' j : ℕ, ((1 / 2 : ℝ≥0∞)) ^ j)
          = (∑' j : ℕ, ((2 : ℝ≥0∞))⁻¹ ^ j) := by
        apply tsum_congr
        intro j
        rw [one_div]
      have hle : (∑' j : ℕ, ((1 / 2 : ℝ≥0∞)) ^ (j + 1))
          ≤ (∑' j : ℕ, ((1 / 2 : ℝ≥0∞)) ^ j) := by
        apply ENNReal.tsum_le_tsum
        intro j
        calc ((1 / 2 : ℝ≥0∞)) ^ (j + 1) = ((1 / 2 : ℝ≥0∞)) ^ j * (1 / 2) := by
              rw [pow_succ]
          _ ≤ ((1 / 2 : ℝ≥0∞)) ^ j * 1 := mul_le_mul_right (by norm_num) _
          _ = ((1 / 2 : ℝ≥0∞)) ^ j := mul_one _
      rw [← key2] at hb
      exact ne_top_of_le_ne_top hb hle
    exact ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun j => (hAle j).le)
  have hae := MeasureTheory.ae_eventually_notMem (μ := mu) (s := A) hsum
  filter_upwards [hae] with omega homega
  refine ⟨phi, hphi_cof, ?_⟩
  intro B hB eps heps
  obtain ⟨J0, hJ0⟩ := eventually_atTop.1 homega
  obtain ⟨m, hm⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : SpatialCoordinates d)).1 hB.isBounded
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / eps)
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkeps : (1 : ℝ) / ((k : ℝ) + 1) < eps := by
    have h2 : (1 : ℝ) / eps < (k : ℝ) + 1 := by linarith [hk]
    rw [div_lt_iff₀ hkpos]
    calc (1 : ℝ) = eps * (1 / eps) := by rw [mul_one_div, div_self (ne_of_gt heps)]
      _ < eps * ((k : ℝ) + 1) := mul_lt_mul_of_pos_left h2 heps
  refine ⟨max J0 (max ⌈m⌉₊ k), ?_⟩
  intro j hj x hxB
  have hJ0j : J0 ≤ j := le_trans (le_max_left _ _) hj
  have hmk : max ⌈m⌉₊ k ≤ j := le_trans (le_max_right _ _) hj
  have hceilj : ⌈m⌉₊ ≤ j := le_trans (le_max_left _ _) hmk
  have hkj : k ≤ j := le_trans (le_max_right _ _) hmk
  have hnotmem : omega ∉ A j := hJ0 j hJ0j
  have hdj : ∀ y ∈ Metric.closedBall (0 : SpatialCoordinates d) ((j : ℝ) + 1),
      pathLevyProkhorovDist
        (jointPathProbabilityMeasure (KN (phi j)) (hKN (phi j)) omega y)
        (jointPathProbabilityMeasure K hK omega y) < (1 : ℝ) / ((j : ℝ) + 1) := by
    intro y hy
    by_contra hcon
    exact hnotmem ⟨y, hy, not_lt.mp hcon⟩
  have hrad : m ≤ (j : ℝ) + 1 := by
    have h1 : (⌈m⌉₊ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hceilj
    have h2 : m ≤ (⌈m⌉₊ : ℝ) := Nat.le_ceil m
    linarith
  have hxB' : x ∈ Metric.closedBall (0 : SpatialCoordinates d) ((j : ℝ) + 1) :=
    Metric.closedBall_subset_closedBall hrad (hm hxB)
  calc pathLevyProkhorovDist
        (jointPathProbabilityMeasure (KN (phi j)) (hKN (phi j)) omega x)
        (jointPathProbabilityMeasure K hK omega x)
      < (1 : ℝ) / ((j : ℝ) + 1) := hdj x hxB'
    _ ≤ (1 : ℝ) / ((k : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
        linarith
    _ < eps := hkeps



theorem aux_prop_limit_properties_symmetry_limit_lp_two_seq {d : ℕ}
    (μ ν : ℕ → ProbabilityMeasure (DiffusionPath d))
    (a : ProbabilityMeasure (DiffusionPath d))
    (hμν : Tendsto (fun k => pathLevyProkhorovDist (μ k) (ν k)) atTop (𝓝 0))
    (hν : Tendsto ν atTop (𝓝 a)) :
    Tendsto μ atTop (𝓝 a) := by
  let : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  have hνe : Tendsto (fun k => (LevyProkhorov.ofMeasure (ν k) :
      LevyProkhorov (ProbabilityMeasure (DiffusionPath d)))) atTop
      (𝓝 (LevyProkhorov.ofMeasure a)) :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto a).comp hν
  have hd : ∀ k, dist (LevyProkhorov.ofMeasure (μ k) :
      LevyProkhorov (ProbabilityMeasure (DiffusionPath d))) (LevyProkhorov.ofMeasure (ν k))
      = pathLevyProkhorovDist (μ k) (ν k) := fun k => LevyProkhorov.dist_probabilityMeasure_def _ _
  have hμe : Tendsto (fun k => (LevyProkhorov.ofMeasure (μ k) :
      LevyProkhorov (ProbabilityMeasure (DiffusionPath d)))) atTop
      (𝓝 (LevyProkhorov.ofMeasure a)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg)
      (fun k => dist_triangle _ (LevyProkhorov.ofMeasure (ν k)) _) ?_
    have h2 := tendsto_iff_dist_tendsto_zero.1 hνe
    have h3 := hμν.add h2
    simp only [add_zero] at h3
    simpa only [hd] using h3
  exact (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp hμe

/-- Proof step of `prop_limit_properties_symmetry_limit`, one compact set of
starting points: uniform Lévy–Prokhorov convergence of the path laws on `B`, together with continuity
of the limit law in the starting point, gives uniform convergence on `B` of the integrals of a bounded
continuous path functional. (Auxiliary lemma; applied at a fixed environment with
`νs j x = jointPathProbabilityMeasure (KN (φ j)) (hKN (φ j)) omega x` and
`ν x = jointPathProbabilityMeasure K hK omega x`.) -/
theorem aux_prop_limit_properties_symmetry_limit_lp_integral_unif {d : ℕ}
    (νs : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (ν : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hcont : Continuous ν)
    (B : Set (SpatialCoordinates d)) (hB : IsCompact B)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ x ∈ B,
      pathLevyProkhorovDist (νs j x) (ν x) < eps)
    (Φ : BoundedContinuousFunction (DiffusionPath d) ℝ) (eps : ℝ) (heps : 0 < eps) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ x ∈ B,
      |∫ path, Φ path ∂(νs j x : Measure (DiffusionPath d)) -
        ∫ path, Φ path ∂(ν x : Measure (DiffusionPath d))| < eps := by
  by_contra hcon
  push Not at hcon
  choose j hj x hxB hbad using hcon
  obtain ⟨xs, hxsB, ψ, hψ, hxlim⟩ := hB.tendsto_subseq hxB
  have hjψ : Tendsto (fun n => j (ψ n)) atTop atTop :=
    tendsto_atTop_mono (fun n => le_trans (hψ.id_le n) (hj (ψ n))) tendsto_id
  have hLP : Tendsto (fun n => pathLevyProkhorovDist (νs (j (ψ n)) (x (ψ n))) (ν (x (ψ n)))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨J, hJ⟩ := hunif e he
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hjψ.eventually_ge_atTop J)
    refine ⟨N, fun n hn => ?_⟩
    have hv : 0 ≤ pathLevyProkhorovDist (νs (j (ψ n)) (x (ψ n))) (ν (x (ψ n))) := ENNReal.toReal_nonneg
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg hv]
    exact hJ (j (ψ n)) (hN n hn) (x (ψ n)) (hxB (ψ n))
  have hνlim : Tendsto (fun n => ν (x (ψ n))) atTop (𝓝 (ν xs)) := (hcont.tendsto xs).comp hxlim
  have hμlim : Tendsto (fun n => νs (j (ψ n)) (x (ψ n))) atTop (𝓝 (ν xs)) :=
    aux_prop_limit_properties_symmetry_limit_lp_two_seq _ _ _ hLP hνlim
  have h1 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμlim Φ
  have h2 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hνlim Φ
  have h3 := (h1.sub h2).abs
  simp only [sub_self, abs_zero] at h3
  obtain ⟨n, hn⟩ := (h3.eventually_lt_const heps).exists
  exact absurd (hbad (ψ n)) (not_le.2 hn)

theorem aux_prop_limit_properties_symmetry_limit_cutoff_localFinite
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) :
    IsLocallyFiniteMeasure (cutoffSpeedMeasure M H omega N) := by
  rw [cutoffSpeedMeasure_eq_weightedChaosCutoff]
  exact weightedChaosCutoff_isLocallyFinite M H N omega

theorem aux_prop_limit_properties_symmetry_limit_ofReal_lintegral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {nu : Measure (SpatialCoordinates d)}
    (hnu : IsLocallyFiniteMeasure nu)
    (f : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂nu) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂nu := by
  let := hnu
  exact ofReal_integral_eq_lintegral_ofReal
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
    (Filter.Eventually.of_forall hf)

theorem aux_prop_limit_properties_symmetry_limit_ofReal_local_convergence
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (muN : ℕ → Measure (SpatialCoordinates d))
    (mu : Measure (SpatialCoordinates d))
    (hmu : MeasuresConvergeLocally muN mu)
    (hmuN : ∀ N, IsLocallyFiniteMeasure (muN N))
    (hmu_lim : IsLocallyFiniteMeasure mu)
    (f : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    Tendsto (fun N ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂muN N) atTop
      (nhds (∫⁻ x, ENNReal.ofReal (f x) ∂mu)) := by
  have hreal := (ENNReal.continuous_ofReal.tendsto (∫ x, f x ∂mu)).comp (hmu f)
  convert hreal using 1
  · funext N
    exact (aux_prop_limit_properties_symmetry_limit_ofReal_lintegral (hmuN N) f hf).symm
  · exact congrArg nhds
      (aux_prop_limit_properties_symmetry_limit_ofReal_lintegral hmu_lim f hf).symm

theorem aux_prop_limit_properties_symmetry_limit_path_eval_lintegral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (Q : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d) (x : SpatialCoordinates d) (t : ℝ≥0)
    (hmap : Q.map (ContinuousPath.finsetEvaluation {t}) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P {t} x)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∫⁻ y, ENNReal.ofReal (f y) ∂P.kernel t x =
      ∫⁻ path, ENNReal.ofReal (f (path t)) ∂Q (omega, x) := by
  have hmarg : Measure.map (fun path : DiffusionPath d => path t) (Q (omega, x)) =
      P.kernel t x := by
    apply SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation P (Q (omega, x)) x t
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)]
    exact hmap
  rw [← hmarg, lintegral_map]
  all_goals
    first
      | exact (continuous_eval_const t).measurable
      | exact (ENNReal.measurable_ofReal.comp f.measurable)

theorem aux_prop_limit_properties_symmetry_limit_ofReal_bcf_lintegral
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {nu : Measure α} [IsFiniteMeasure nu]
    (f : BoundedContinuousFunction α ℝ) (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂nu) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂nu := by
  exact ofReal_integral_eq_lintegral_ofReal (f.integrable nu)
    (Filter.Eventually.of_forall hf)

theorem aux_prop_limit_properties_symmetry_limit_ccomp_to_bcf
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (f : C_c(SpatialCoordinates d, ℝ)) :
    ∃ F : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x, F x = f x := by
  have hb : Bornology.IsBounded (Set.range f) :=
    (f.hasCompactSupport.isCompact_range f.continuous).isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hb
  refine ⟨BoundedContinuousFunction.mk f.toContinuousMap ?_, ?_⟩
  · exact ⟨C, fun x y => hC ⟨x, rfl⟩ ⟨y, rfl⟩⟩
  · intro x
    rfl

theorem aux_prop_limit_properties_symmetry_limit_ccomp_eval_bcf
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (f : C_c(SpatialCoordinates d, ℝ)) (t : ℝ≥0) :
    ∃ F : BoundedContinuousFunction (DiffusionPath d) ℝ,
      ∀ path, F path = f (path t) := by
  obtain ⟨F, hF⟩ := aux_prop_limit_properties_symmetry_limit_ccomp_to_bcf f
  refine ⟨F.compContinuous ⟨(fun path : DiffusionPath d => path t),
    continuous_eval_const t⟩, ?_⟩
  intro path
  exact hF (path t)



theorem aux_prop_limit_properties_symmetry_limit_marginal_cont {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (omega : BilateralField d)
    (hfdd : ∀ (I : Finset ℝ≥0) (x : SpatialCoordinates d),
      K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (hcont : Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure K hK omega x))
    (t : ℝ≥0) (G : C_c(SpatialCoordinates d, ℝ))
    (Φ : BoundedContinuousFunction (DiffusionPath d) ℝ)
    (hΦ : ∀ path : DiffusionPath d, Φ path = G (path t)) :
    (∀ x : SpatialCoordinates d, ∫ y, G y ∂(P t x) =
        ∫ path, Φ path ∂(jointPathProbabilityMeasure K hK omega x : Measure (DiffusionPath d))) ∧
      Continuous (fun x : SpatialCoordinates d => ∫ y, G y ∂(P t x)) := by
  have hev : Measurable (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) ({t} : Finset ℝ≥0)) :=
    Measurable.of_eval fun s => (continuous_eval_const ((s : ℝ≥0))).measurable
  have hmarg : ∀ x : SpatialCoordinates d, (K (omega, x)).map (fun path : DiffusionPath d => path t) = P t x := by
    intro x
    apply SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation P (K (omega, x)) x t
    rw [← Kernel.map_apply K hev (omega, x)]
    exact hfdd {t} x
  have hid : ∀ x : SpatialCoordinates d, ∫ y, G y ∂(P t x) =
      ∫ path, Φ path ∂(jointPathProbabilityMeasure K hK omega x : Measure (DiffusionPath d)) := by
    intro x
    calc ∫ y, G y ∂(P t x)
        = ∫ y, G y ∂(Measure.map (fun path : DiffusionPath d => path t) (K (omega, x))) := by
            rw [← hmarg x]
      _ = ∫ path, G (path t) ∂(K (omega, x)) :=
            integral_map (continuous_eval_const t).measurable.aemeasurable G.continuous.aestronglyMeasurable
      _ = ∫ path, Φ path ∂(K (omega, x)) := by simp only [hΦ]
      _ = ∫ path, Φ path ∂(jointPathProbabilityMeasure K hK omega x : Measure (DiffusionPath d)) := rfl
  refine ⟨hid, ?_⟩
  have hfun : (fun x : SpatialCoordinates d => ∫ y, G y ∂(P t x)) =
      fun x => ∫ path, Φ path ∂(jointPathProbabilityMeasure K hK omega x : Measure (DiffusionPath d)) := funext hid
  rw [hfun, continuous_iff_continuousAt]
  intro x
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (hcont.tendsto x) Φ

theorem aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_err {d : ℕ}
    (μs : ℕ → Measure (SpatialCoordinates d))
    (hμs : ∀ j, IsLocallyFiniteMeasure (μs j))
    (F : SpatialCoordinates d →C_c ℝ)
    (hs : ℕ → SpatialCoordinates d → ℝ) (h : SpatialCoordinates d → ℝ)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ∀ x ∈ tsupport (F : SpatialCoordinates d → ℝ), |hs j x - h x| < eps)
    (A : ℝ) (hA0 : 0 ≤ A)
    (hA : Tendsto (fun j => ∫ x, |F x| ∂μs j) atTop (𝓝 A)) :
    Tendsto (fun j => ∫ x, F x * (hs j x - h x) ∂μs j) atTop (𝓝 0) := by
  have hiabs : ∀ j, Integrable (fun x => |F x|) (μs j) := by
    intro j
    have := hμs j
    exact Continuous.integrable_of_hasCompactSupport F.continuous.abs
      (F.hasCompactSupport.comp_left abs_zero)
  have hAev : ∀ᶠ j in atTop, ∫ x, |F x| ∂μs j ≤ A + 1 :=
    hA.eventually_le_const (by linarith)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc : 0 < ε / (2 * (A + 1)) := by
    apply div_pos hε
    have : 0 < A + 1 := by linarith
    positivity
  obtain ⟨J, hJ⟩ := hunif _ hc
  obtain ⟨J', hJ'⟩ := Filter.eventually_atTop.1 hAev
  refine ⟨max J J', fun j hj => ?_⟩
  rw [dist_zero_right]
  have hpt : ∀ x, ‖F x * (hs j x - h x)‖ ≤ ε / (2 * (A + 1)) * |F x| := by
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : x ∈ tsupport (F : SpatialCoordinates d → ℝ)
    · have h1 : |hs j x - h x| < ε / (2 * (A + 1)) := hJ j (le_of_max_le_left hj) x hx
      rw [mul_comm (|F x|)]
      exact mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  calc ‖∫ x, F x * (hs j x - h x) ∂μs j‖
      ≤ ∫ x, ε / (2 * (A + 1)) * |F x| ∂μs j :=
        norm_integral_le_of_norm_le ((hiabs j).const_mul (ε / (2 * (A + 1))))
          (Filter.Eventually.of_forall hpt)
    _ = ε / (2 * (A + 1)) * ∫ x, |F x| ∂μs j := integral_const_mul _ _
    _ ≤ ε / (2 * (A + 1)) * (A + 1) :=
        mul_le_mul_of_nonneg_left (hJ' j (le_of_max_le_right hj)) hc.le
    _ < ε := by
        rw [div_mul_eq_mul_div]
        rw [div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (A + 1))]
        exact mul_lt_mul_of_pos_left (by linarith) hε

theorem aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_absl {d : ℕ}
    (μs : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    (hconv : ∀ f : SpatialCoordinates d →C_c ℝ,
      Tendsto (fun j => ∫ x, f x ∂μs j) atTop (𝓝 (∫ x, f x ∂μ)))
    (F : SpatialCoordinates d →C_c ℝ) :
    Tendsto (fun j => ∫ x, |F x| ∂μs j) atTop (𝓝 (∫ x, |F x| ∂μ)) :=
  hconv ⟨⟨fun x => |F x|, F.continuous.abs⟩, F.hasCompactSupport.comp_left abs_zero⟩

theorem aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_hFh {d : ℕ}
    (μs : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    (hconv : ∀ f : SpatialCoordinates d →C_c ℝ,
      Tendsto (fun j => ∫ x, f x ∂μs j) atTop (𝓝 (∫ x, f x ∂μ)))
    (F : SpatialCoordinates d →C_c ℝ) (h : SpatialCoordinates d → ℝ) (hh : Continuous h) :
    Tendsto (fun j => ∫ x, F x * h x ∂μs j) atTop (𝓝 (∫ x, F x * h x ∂μ)) :=
  hconv ⟨⟨fun x => F x * h x, F.continuous.mul hh⟩, F.hasCompactSupport.mul_right⟩

theorem aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_split {d : ℕ}
    (μs : ℕ → Measure (SpatialCoordinates d)) (hμs : ∀ j, IsLocallyFiniteMeasure (μs j))
    (F : SpatialCoordinates d →C_c ℝ)
    (hs : ℕ → SpatialCoordinates d → ℝ) (h : SpatialCoordinates d → ℝ)
    (hhs : ∀ j, Continuous (hs j)) (hh : Continuous h) :
    ∀ j, ∫ x, F x * (hs j x - h x) ∂μs j + ∫ x, F x * h x ∂μs j
      = ∫ x, F x * hs j x ∂μs j := by
  intro j
  have hidiff : Integrable (fun x => F x * (hs j x - h x)) (μs j) := by
    have := hμs j
    exact Continuous.integrable_of_hasCompactSupport (F.continuous.mul ((hhs j).sub hh))
      F.hasCompactSupport.mul_right
  have hih : Integrable (fun x => F x * h x) (μs j) := by
    have := hμs j
    exact Continuous.integrable_of_hasCompactSupport (F.continuous.mul hh)
      F.hasCompactSupport.mul_right
  rw [← integral_add hidiff hih]
  congr 1
  funext x
  ring

theorem aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_combine {d : ℕ}
    (μs : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    (F : SpatialCoordinates d →C_c ℝ)
    (hs : ℕ → SpatialCoordinates d → ℝ) (h : SpatialCoordinates d → ℝ)
    (herr : Tendsto (fun j => ∫ x, F x * (hs j x - h x) ∂μs j) atTop (𝓝 0))
    (hFh : Tendsto (fun j => ∫ x, F x * h x ∂μs j) atTop (𝓝 (∫ x, F x * h x ∂μ)))
    (hsplit : ∀ j, ∫ x, F x * (hs j x - h x) ∂μs j + ∫ x, F x * h x ∂μs j
      = ∫ x, F x * hs j x ∂μs j) :
    Tendsto (fun j => ∫ x, F x * hs j x ∂μs j) atTop (𝓝 (∫ x, F x * h x ∂μ)) := by
  have hsum : Tendsto (fun j => ∫ x, F x * (hs j x - h x) ∂μs j + ∫ x, F x * h x ∂μs j)
      atTop (𝓝 (0 + ∫ x, F x * h x ∂μ)) := herr.add hFh
  rw [zero_add] at hsum
  exact hsum.congr hsplit



theorem aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto {d : ℕ}
    (μs : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    (hμs : ∀ j, IsLocallyFiniteMeasure (μs j))
    (hconv : ∀ f : C_c(SpatialCoordinates d, ℝ),
      Tendsto (fun j => ∫ x, f x ∂μs j) atTop (𝓝 (∫ x, f x ∂μ)))
    (F : C_c(SpatialCoordinates d, ℝ))
    (hs : ℕ → SpatialCoordinates d → ℝ) (h : SpatialCoordinates d → ℝ)
    (hhs : ∀ j, Continuous (hs j)) (hh : Continuous h)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ∀ x ∈ tsupport (F : SpatialCoordinates d → ℝ), |hs j x - h x| < eps) :
    Tendsto (fun j => ∫ x, F x * hs j x ∂μs j) atTop (𝓝 (∫ x, F x * h x ∂μ)) := by
  have hFh := aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_hFh μs μ hconv F h hh
  have hAabs := aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_absl μs μ hconv F
  have hA0 : 0 ≤ ∫ x, |F x| ∂μ := integral_nonneg (fun x => abs_nonneg _)
  have herr := aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_err μs hμs F hs h
    hunif (∫ x, |F x| ∂μ) hA0 hAabs
  exact aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_combine μs μ F hs h herr hFh
    (aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto_split μs hμs F hs h hhs hh)



theorem aux_prop_limit_properties_symmetry_limit_cc_lintegral_eq {d : ℕ}
    {μ : Measure (SpatialCoordinates d)} (hμ : IsLocallyFiniteMeasure μ)
    {κ : Kernel (SpatialCoordinates d) (SpatialCoordinates d)} (hsub : IsSubMarkovKernel κ)
    (F G : C_c(SpatialCoordinates d, ℝ)) (hF : ∀ x, 0 ≤ F x) (hG : ∀ x, 0 ≤ G x)
    (hcont : Continuous fun x => ∫ y, G y ∂κ x) :
    ∫⁻ x, ENNReal.ofReal (F x) * ∫⁻ y, ENNReal.ofReal (G y) ∂κ x ∂μ =
      ENNReal.ofReal (∫ x, F x * ∫ y, G y ∂κ x ∂μ) := by
  have := hμ
  have : IsFiniteKernel κ := hsub.isFiniteKernel
  have hpt : ∀ x, ENNReal.ofReal (F x) * ∫⁻ y, ENNReal.ofReal (G y) ∂κ x
      = ENNReal.ofReal (F x * ∫ y, G y ∂κ x) := by
    intro x
    have hGi : Integrable (fun y => G y) (κ x) :=
      G.continuous.integrable_of_hasCompactSupport G.hasCompactSupport
    rw [← ofReal_integral_eq_lintegral_ofReal hGi (Filter.Eventually.of_forall hG),
      ENNReal.ofReal_mul (hF x)]
  rw [lintegral_congr hpt]
  refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
  · exact (F.continuous.mul hcont).integrable_of_hasCompactSupport F.hasCompactSupport.mul_right
  · exact Filter.Eventually.of_forall fun x => mul_nonneg (hF x) (integral_nonneg fun y => hG y)



theorem aux_prop_limit_properties_symmetry_limit_cutoff_cc {d : ℕ}
    {μ : Measure (SpatialCoordinates d)} (hμ : IsLocallyFiniteMeasure μ)
    (Q : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hQ : SemigroupSymmetric Q μ)
    (t : ℝ≥0) (F G : C_c(SpatialCoordinates d, ℝ)) (hF : ∀ x, 0 ≤ F x) (hG : ∀ x, 0 ≤ G x)
    (hcF : Continuous fun x => ∫ y, F y ∂Q t x) (hcG : Continuous fun x => ∫ y, G y ∂Q t x) :
    ∫ x, F x * ∫ y, G y ∂Q t x ∂μ = ∫ x, G x * ∫ y, F y ∂Q t x ∂μ := by
  have h := hQ t (fun x => ENNReal.ofReal (F x)) (fun x => ENNReal.ofReal (G x))
    (ENNReal.measurable_ofReal.comp F.continuous.measurable)
    (ENNReal.measurable_ofReal.comp G.continuous.measurable)
  rw [aux_prop_limit_properties_symmetry_limit_cc_lintegral_eq hμ (Q.isSubMarkovKernel t)
      F G hF hG hcG,
    aux_prop_limit_properties_symmetry_limit_cc_lintegral_eq hμ (Q.isSubMarkovKernel t)
      G F hG hF hcF] at h
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg fun x => mul_nonneg (hF x) (integral_nonneg fun y => hG y))
    (integral_nonneg fun x => mul_nonneg (hG x) (integral_nonneg fun y => hF y))).1 h



theorem aux_prop_limit_properties_symmetry_limit_side_tendsto
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (PN : ℕ → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (omega : BilateralField d)
    (hlim : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (hattach : ∀ N (I : Finset ℝ≥0) (x : SpatialCoordinates d),
      (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N) I x)
    (hstartN : ∀ N, Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure (KN N) (hKN N) omega x))
    (hstart : Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure K hK omega x))
    (φ : ℕ → ℕ)
    (hunifφ : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∃ J : ℕ, ∀ j ≥ J, ∀ x ∈ B,
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN (φ j)) (hKN (φ j)) omega x)
          (jointPathProbabilityMeasure K hK omega x) < eps)
    (μs : ℕ → Measure (SpatialCoordinates d)) (hμs : ∀ j, IsLocallyFiniteMeasure (μs j))
    (μ : Measure (SpatialCoordinates d))
    (hconv : ∀ f : C_c(SpatialCoordinates d, ℝ),
      Tendsto (fun j => ∫ x, f x ∂μs j) atTop (𝓝 (∫ x, f x ∂μ)))
    (t : ℝ≥0) (F G : C_c(SpatialCoordinates d, ℝ)) :
    Tendsto (fun j => ∫ x, F x * ∫ y, G y ∂(PN (φ j) t x) ∂μs j) atTop
      (𝓝 (∫ x, F x * ∫ y, G y ∂(P t x) ∂μ)) := by
  obtain ⟨Φ, hΦ⟩ := aux_prop_limit_properties_symmetry_limit_ccomp_eval_bcf G t
  have hmc := aux_prop_limit_properties_symmetry_limit_marginal_cont K hK P omega hlim hstart
    t G Φ hΦ
  have hmcN : ∀ j, _ := fun j => aux_prop_limit_properties_symmetry_limit_marginal_cont
    (KN (φ j)) (hKN (φ j)) (PN (φ j)) omega (hattach (φ j)) (hstartN (φ j)) t G Φ hΦ
  refine aux_prop_limit_properties_symmetry_limit_cc_mul_tendsto μs μ hμs hconv F
    (fun j x => ∫ y, G y ∂(PN (φ j) t x)) (fun x => ∫ y, G y ∂(P t x))
    (fun j => (hmcN j).2) hmc.2 ?_
  intro eps heps
  obtain ⟨J, hJ⟩ := aux_prop_limit_properties_symmetry_limit_lp_integral_unif
    (fun j x => jointPathProbabilityMeasure (KN (φ j)) (hKN (φ j)) omega x)
    (fun x => jointPathProbabilityMeasure K hK omega x) hstart
    (tsupport (F : SpatialCoordinates d → ℝ)) F.hasCompactSupport.isCompact
    (fun e he => hunifφ _ F.hasCompactSupport.isCompact e he) Φ eps heps
  refine ⟨J, fun j hj x hx => ?_⟩
  rw [(hmcN j).1 x, hmc.1 x]
  exact hJ j hj x hx



theorem aux_prop_limit_properties_symmetry_limit_limit_cc
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (PN : ℕ → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (omega : BilateralField d)
    (hlim : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (hattach : ∀ N (I : Finset ℝ≥0) (x : SpatialCoordinates d),
      (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N) I x)
    (hstartN : ∀ N, Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure (KN N) (hKN N) omega x))
    (hstart : Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure K hK omega x))
    (μN : ℕ → Measure (SpatialCoordinates d)) (hμN : ∀ N, IsLocallyFiniteMeasure (μN N))
    (hsymN : ∀ N, SemigroupSymmetric (PN N) (μN N))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (hunifφ : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∃ J : ℕ, ∀ j ≥ J, ∀ x ∈ B,
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN (φ j)) (hKN (φ j)) omega x)
          (jointPathProbabilityMeasure K hK omega x) < eps)
    (μ : Measure (SpatialCoordinates d)) (hμconv : MeasuresConvergeLocally μN μ)
    (t : ℝ≥0) (F G : C_c(SpatialCoordinates d, ℝ)) (hF : ∀ x, 0 ≤ F x) (hG : ∀ x, 0 ≤ G x) :
    ∫ x, F x * ∫ y, G y ∂(P t x) ∂μ = ∫ x, G x * ∫ y, F y ∂(P t x) ∂μ := by
  have hconv : ∀ f : C_c(SpatialCoordinates d, ℝ),
      Tendsto (fun j => ∫ x, f x ∂μN (φ j)) atTop (𝓝 (∫ x, f x ∂μ)) :=
    fun f => (hμconv f).comp hφ
  have h1 := aux_prop_limit_properties_symmetry_limit_side_tendsto KN hKN K hK PN P omega
    hlim hattach hstartN hstart φ hunifφ (fun j => μN (φ j)) (fun j => hμN (φ j)) μ hconv t F G
  have h2 := aux_prop_limit_properties_symmetry_limit_side_tendsto KN hKN K hK PN P omega
    hlim hattach hstartN hstart φ hunifφ (fun j => μN (φ j)) (fun j => hμN (φ j)) μ hconv t G F
  obtain ⟨ΦF, hΦF⟩ := aux_prop_limit_properties_symmetry_limit_ccomp_eval_bcf F t
  obtain ⟨ΦG, hΦG⟩ := aux_prop_limit_properties_symmetry_limit_ccomp_eval_bcf G t
  have heq : ∀ j, ∫ x, F x * ∫ y, G y ∂(PN (φ j) t x) ∂μN (φ j) =
      ∫ x, G x * ∫ y, F y ∂(PN (φ j) t x) ∂μN (φ j) := fun j =>
    aux_prop_limit_properties_symmetry_limit_cutoff_cc (hμN (φ j)) (PN (φ j)) (hsymN (φ j)) t
      F G hF hG
      (aux_prop_limit_properties_symmetry_limit_marginal_cont (KN (φ j)) (hKN (φ j)) (PN (φ j))
        omega (hattach (φ j)) (hstartN (φ j)) t F ΦF hΦF).2
      (aux_prop_limit_properties_symmetry_limit_marginal_cont (KN (φ j)) (hKN (φ j)) (PN (φ j))
        omega (hattach (φ j)) (hstartN (φ j)) t G ΦG hΦG).2
  exact tendsto_nhds_unique (h1.congr heq) h2



theorem aux_prop_limit_properties_symmetry_limit_urysohn_eventually {d : ℕ}
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U) (x : SpatialCoordinates d) :
    ∀ᶠ n in atTop, ENNReal.ofReal (urysohnSeq hU n x) = U.indicator 1 x := by
  by_cases hx : x ∈ U
  · have hx' := hx
    rw [← iUnion_openPiece hU] at hx'
    obtain ⟨n0, hn0⟩ := Set.mem_iUnion.1 hx'
    filter_upwards [eventually_ge_atTop n0] with n hn
    rw [(urysohnSeq_spec hU n).2.1 x (monotone_openPiece U hn hn0), Set.indicator_of_mem hx]
    simp
  · refine Filter.Eventually.of_forall fun n => ?_
    have h0 : urysohnSeq hU n x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hxs => hx ((urysohnSeq_spec hU n).2.2 hxs)
    rw [h0, Set.indicator_of_notMem hx]
    simp

theorem aux_prop_limit_properties_symmetry_limit_urysohn_le {d : ℕ}
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U) (n : ℕ) (x : SpatialCoordinates d) :
    ENNReal.ofReal (urysohnSeq hU n x) ≤ U.indicator 1 x := by
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx]
    simpa using ENNReal.ofReal_le_ofReal ((urysohnSeq_spec hU n).1 x).2
  · have h0 : urysohnSeq hU n x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hxs => hx ((urysohnSeq_spec hU n).2.2 hxs)
    rw [h0, Set.indicator_of_notMem hx]
    simp

theorem aux_prop_limit_properties_symmetry_limit_urysohn_inner {d : ℕ}
    {κ : Kernel (SpatialCoordinates d) (SpatialCoordinates d)} (hsub : IsSubMarkovKernel κ)
    {D : Set (SpatialCoordinates d)} (hD : IsOpen D) (x : SpatialCoordinates d) :
    Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (urysohnSeq hD n y) ∂κ x) atTop (𝓝 (κ x D)) := by
  have hfin : ∫⁻ y, D.indicator 1 y ∂κ x ≠ ⊤ := by
    rw [lintegral_indicator_one hD.measurableSet]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (hsub.measure_le_one x D)
  have h := tendsto_lintegral_of_dominated_convergence (μ := κ x) (D.indicator 1)
    (fun n => ENNReal.measurable_ofReal.comp (urysohnSeq hD n).continuous.measurable)
    (fun n => Filter.Eventually.of_forall
      (aux_prop_limit_properties_symmetry_limit_urysohn_le hD n))
    hfin (Filter.Eventually.of_forall fun y =>
      tendsto_const_nhds.congr' ((aux_prop_limit_properties_symmetry_limit_urysohn_eventually
        hD y).mono fun n hn => hn.symm))
  rwa [lintegral_indicator_one hD.measurableSet] at h

theorem aux_prop_limit_properties_symmetry_limit_urysohn_outer {d : ℕ}
    {μ : Measure (SpatialCoordinates d)}
    {κ : Kernel (SpatialCoordinates d) (SpatialCoordinates d)} (hsub : IsSubMarkovKernel κ)
    {C D : Set (SpatialCoordinates d)} (hC : IsOpen C) (hD : IsOpen D) (hCf : μ C ≠ ⊤) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (urysohnSeq hC n x) *
        ∫⁻ y, ENNReal.ofReal (urysohnSeq hD n y) ∂κ x ∂μ) atTop
      (𝓝 (∫⁻ x in C, κ x D ∂μ)) := by
  have hlimint : ∫⁻ x in C, κ x D ∂μ = ∫⁻ x, C.indicator 1 x * κ x D ∂μ := by
    rw [← lintegral_indicator hC.measurableSet]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ C <;> simp [hx]
  rw [hlimint]
  have hin_le : ∀ n x, ∫⁻ y, ENNReal.ofReal (urysohnSeq hD n y) ∂κ x ≤ 1 := by
    intro n x
    calc ∫⁻ y, ENNReal.ofReal (urysohnSeq hD n y) ∂κ x ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂κ x := by
          refine lintegral_mono fun y => ?_
          simpa using ENNReal.ofReal_le_ofReal ((urysohnSeq_spec hD n).1 y).2
      _ = κ x Set.univ := lintegral_one
      _ ≤ 1 := hsub.measure_le_one x Set.univ
  refine tendsto_lintegral_of_dominated_convergence (C.indicator 1)
    (fun n => (ENNReal.measurable_ofReal.comp (urysohnSeq hC n).continuous.measurable).mul
      (Measurable.lintegral_kernel
        (ENNReal.measurable_ofReal.comp (urysohnSeq hD n).continuous.measurable)))
    (fun n => Filter.Eventually.of_forall fun x => ?_) ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · calc ENNReal.ofReal (urysohnSeq hC n x) * ∫⁻ y, ENNReal.ofReal (urysohnSeq hD n y) ∂κ x
        ≤ C.indicator 1 x * 1 :=
          mul_le_mul' (aux_prop_limit_properties_symmetry_limit_urysohn_le hC n x)
            (hin_le n x)
      _ = C.indicator 1 x := mul_one _
  · rw [lintegral_indicator_one hC.measurableSet]
    exact hCf
  · have hne : C.indicator (1 : SpatialCoordinates d → ℝ≥0∞) x ≠ ⊤ := by
      by_cases hx : x ∈ C <;> simp [hx]
    refine (ENNReal.Tendsto.const_mul
      (aux_prop_limit_properties_symmetry_limit_urysohn_inner hsub hD x) (Or.inr hne)).congr' ?_
    filter_upwards [aux_prop_limit_properties_symmetry_limit_urysohn_eventually hC x] with n hn
    rw [hn]



theorem aux_prop_limit_properties_symmetry_limit_cc_to_open {d : ℕ}
    {μ : Measure (SpatialCoordinates d)}
    {κ : Kernel (SpatialCoordinates d) (SpatialCoordinates d)} (hsub : IsSubMarkovKernel κ)
    (hcc : ∀ F G : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ F x) → (∀ x, 0 ≤ G x) →
      ∫⁻ x, ENNReal.ofReal (F x) * ∫⁻ y, ENNReal.ofReal (G y) ∂κ x ∂μ =
        ∫⁻ x, ENNReal.ofReal (G x) * ∫⁻ y, ENNReal.ofReal (F y) ∂κ x ∂μ)
    {C D : Set (SpatialCoordinates d)} (hC : IsOpen C) (hD : IsOpen D)
    (hCf : μ C ≠ ⊤) (hDf : μ D ≠ ⊤) :
    ∫⁻ x in C, κ x D ∂μ = ∫⁻ x in D, κ x C ∂μ :=
  tendsto_nhds_unique
    ((aux_prop_limit_properties_symmetry_limit_urysohn_outer hsub hC hD hCf).congr
      fun n => hcc _ _ (urysohnSeq_nonneg hC n) (urysohnSeq_nonneg hD n))
    (aux_prop_limit_properties_symmetry_limit_urysohn_outer hsub hD hC hDf)



theorem aux_prop_limit_properties_symmetry_limit_bdd_open_gen {d : ℕ} :
    (inferInstance : MeasurableSpace (SpatialCoordinates d)) =
      MeasurableSpace.generateFrom
        {U : Set (SpatialCoordinates d) | IsOpen U ∧ Bornology.IsBounded U} := by
  refine (BorelSpace.measurable_eq (α := SpatialCoordinates d)).trans ?_
  rw [borel]
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le fun U hU => ?_
    have hUeq : U = ⋃ n : ℕ, U ∩ Metric.ball (0 : SpatialCoordinates d) (n + 1) := by
      rw [← Set.inter_iUnion, Metric.iUnion_ball_nat_succ, Set.inter_univ]
    rw [hUeq]
    exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
      ⟨(show IsOpen U from hU).inter Metric.isOpen_ball,
        Metric.isBounded_ball.subset Set.inter_subset_right⟩
  · exact MeasurableSpace.generateFrom_le fun U hU =>
      MeasurableSpace.measurableSet_generateFrom hU.1

theorem aux_prop_limit_properties_symmetry_limit_bdd_open_prod_gen {d : ℕ} :
    (inferInstance : MeasurableSpace (SpatialCoordinates d × SpatialCoordinates d)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·)
        {U : Set (SpatialCoordinates d) | IsOpen U ∧ Bornology.IsBounded U}
        {U : Set (SpatialCoordinates d) | IsOpen U ∧ Bornology.IsBounded U}) := by
  have hspan : IsCountablySpanning
      {U : Set (SpatialCoordinates d) | IsOpen U ∧ Bornology.IsBounded U} :=
    ⟨fun n : ℕ => Metric.ball (0 : SpatialCoordinates d) (n + 1),
      fun n => ⟨Metric.isOpen_ball, Metric.isBounded_ball⟩, Metric.iUnion_ball_nat_succ 0⟩
  rw [← generateFrom_prod_eq hspan hspan, ← aux_prop_limit_properties_symmetry_limit_bdd_open_gen]



theorem aux_prop_limit_properties_symmetry_limit_bdd_open_to_measurable {d : ℕ}
    {μ : Measure (SpatialCoordinates d)} (hμ : IsLocallyFiniteMeasure μ)
    {κ : Kernel (SpatialCoordinates d) (SpatialCoordinates d)} (hsub : IsSubMarkovKernel κ)
    (hrect : ∀ C D : Set (SpatialCoordinates d), IsOpen C → Bornology.IsBounded C →
      IsOpen D → Bornology.IsBounded D → ∫⁻ x in C, κ x D ∂μ = ∫⁻ x in D, κ x C ∂μ) :
    ∀ f g : SpatialCoordinates d → ℝ≥0∞, Measurable f → Measurable g →
      ∫⁻ x, f x * (∫⁻ y, g y ∂κ x) ∂μ = ∫⁻ x, g x * (∫⁻ y, f y ∂κ x) ∂μ := by
  have := hμ
  have : IsFiniteKernel κ := hsub.isFiniteKernel
  let S : Set (Set (SpatialCoordinates d)) := {U | IsOpen U ∧ Bornology.IsBounded U}
  let ν : Measure (SpatialCoordinates d × SpatialCoordinates d) := μ.compProd κ
  have hSpi : IsPiSystem S :=
    fun s hs t ht _ => ⟨hs.1.inter ht.1, hs.2.subset Set.inter_subset_left⟩
  have hball : ∀ n : ℕ, Metric.ball (0 : SpatialCoordinates d) (n + 1) ∈ S :=
    fun n => ⟨Metric.isOpen_ball, Metric.isBounded_ball⟩
  have hmono : Monotone fun n : ℕ => Metric.ball (0 : SpatialCoordinates d) (n + 1) := by
    intro m n hmn
    exact Metric.ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hν : ν = Measure.map Prod.swap ν := by
    refine Measure.ext_of_generateFrom_of_iUnion (Set.image2 (· ×ˢ ·) S S)
      (fun n : ℕ => Metric.ball (0 : SpatialCoordinates d) (n + 1) ×ˢ
        Metric.ball (0 : SpatialCoordinates d) (n + 1))
      aux_prop_limit_properties_symmetry_limit_bdd_open_prod_gen (hSpi.prod hSpi) ?_
      (fun n => ⟨_, hball n, _, hball n, rfl⟩) ?_ ?_
    · rw [Set.iUnion_prod_of_monotone hmono hmono, Metric.iUnion_ball_nat_succ,
        Set.univ_prod_univ]
    · intro n
      rw [Measure.compProd_apply_prod Metric.isOpen_ball.measurableSet
        Metric.isOpen_ball.measurableSet]
      refine ne_top_of_le_ne_top (measure_ball_lt_top (μ := μ)
        (x := (0 : SpatialCoordinates d)) (r := (n : ℝ) + 1)).ne ?_
      calc (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (n + 1),
            κ x (Metric.ball (0 : SpatialCoordinates d) (n + 1)) ∂μ)
          ≤ ∫⁻ _x in Metric.ball (0 : SpatialCoordinates d) (n + 1), (1 : ℝ≥0∞) ∂μ :=
            lintegral_mono fun x => hsub.measure_le_one x _
        _ = μ (Metric.ball (0 : SpatialCoordinates d) (n + 1)) := by simp
    · rintro s ⟨A, hA, B, hB, rfl⟩
      rw [Measure.compProd_apply_prod hA.1.measurableSet hB.1.measurableSet,
        Measure.map_apply measurable_swap (hA.1.measurableSet.prod hB.1.measurableSet),
        Set.preimage_swap_prod,
        Measure.compProd_apply_prod hB.1.measurableSet hA.1.measurableSet]
      exact hrect A B hA.1 hA.2 hB.1 hB.2
  have hrect' : ∀ C D : Set (SpatialCoordinates d), MeasurableSet C → MeasurableSet D →
      ∫⁻ x in C, κ x D ∂μ = ∫⁻ x in D, κ x C ∂μ := by
    intro C D hC hD
    calc ∫⁻ x in C, κ x D ∂μ = ν (C ×ˢ D) := (Measure.compProd_apply_prod hC hD).symm
      _ = Measure.map Prod.swap ν (C ×ˢ D) := by rw [← hν]
      _ = ν (D ×ˢ C) := by
        rw [Measure.map_apply measurable_swap (hC.prod hD), Set.preimage_swap_prod]
      _ = ∫⁻ x in D, κ x C ∂μ := Measure.compProd_apply_prod hD hC
  exact aux_prop_limit_properties_cutoff_symmetry_rectangle_to_measurable hsub hrect'
    (fun j : ℕ => Metric.ball (0 : SpatialCoordinates d) (j + 1))
    (fun j => Metric.isOpen_ball.measurableSet) (Metric.iUnion_ball_nat_succ 0)
    (fun j => measure_ball_lt_top.ne)



theorem aux_prop_limit_properties_symmetry_limit_fixed
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (PN : ℕ → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (omega : BilateralField d)
    (hlim : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (hattach : ∀ N (I : Finset ℝ≥0) (x : SpatialCoordinates d),
      (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N) I x)
    (hstartN : ∀ N, Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure (KN N) (hKN N) omega x))
    (hstart : Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure K hK omega x))
    (μN : ℕ → Measure (SpatialCoordinates d)) (hμN : ∀ N, IsLocallyFiniteMeasure (μN N))
    (hsymN : ∀ N, SemigroupSymmetric (PN N) (μN N))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (hunifφ : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∃ J : ℕ, ∀ j ≥ J, ∀ x ∈ B,
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN (φ j)) (hKN (φ j)) omega x)
          (jointPathProbabilityMeasure K hK omega x) < eps)
    (μ : Measure (SpatialCoordinates d)) (hμconv : MeasuresConvergeLocally μN μ)
    (hμ : IsLocallyFiniteMeasure μ) :
    SemigroupSymmetric P μ := by
  intro t
  have hsub := P.isSubMarkovKernel t
  have hcont : ∀ G : C_c(SpatialCoordinates d, ℝ),
      Continuous fun x => ∫ y, G y ∂(P t x) := by
    intro G
    obtain ⟨Φ, hΦ⟩ := aux_prop_limit_properties_symmetry_limit_ccomp_eval_bcf G t
    exact (aux_prop_limit_properties_symmetry_limit_marginal_cont K hK P omega hlim hstart
      t G Φ hΦ).2
  refine aux_prop_limit_properties_symmetry_limit_bdd_open_to_measurable hμ hsub ?_
  intro C D hC hCb hD hDb
  have := hμ
  refine aux_prop_limit_properties_symmetry_limit_cc_to_open hsub ?_ hC hD
    hCb.measure_lt_top.ne hDb.measure_lt_top.ne
  intro F G hF hG
  rw [aux_prop_limit_properties_symmetry_limit_cc_lintegral_eq hμ hsub F G hF hG (hcont G),
    aux_prop_limit_properties_symmetry_limit_cc_lintegral_eq hμ hsub G F hG hF (hcont F),
    aux_prop_limit_properties_symmetry_limit_limit_cc KN hKN K hK PN P omega hlim hattach
      hstartN hstart μN hμN hsymN φ hφ hunifφ μ hμconv t F G hF hG]



theorem prop_limit_properties_symmetry_limit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (hconv : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      Tendsto (fun N ↦ (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)}) atTop (nhds 0))
    (hattach : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N (I : Finset ℝ≥0) (x : SpatialCoordinates d),
        (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (hstartN : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x))
    (hstart : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure K hK omega x))
    (hcutoff : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SemigroupSymmetric (PN N omega) (cutoffSpeedMeasure M H omega N)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ mu : Measure (SpatialCoordinates d),
        MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu →
        IsLocallyFiniteMeasure mu → SemigroupSymmetric (P omega) mu := by
  have hsubseq := aux_prop_limit_properties_symmetry_limit_subseq M KN hKN K hK hconv
  filter_upwards [hlim, hattach, hstartN, hstart, hcutoff, hsubseq]
    with omega hlimω hattω hstNω hstω hcutω hsubω
  intro mu hmu hmulf
  obtain ⟨φ, hφ, hunifφ⟩ := hsubω
  exact aux_prop_limit_properties_symmetry_limit_fixed KN hKN K hK (fun N => PN N omega)
    (P omega) omega hlimω hattω hstNω hstω (fun N => cutoffSpeedMeasure M H omega N)
    (fun N => aux_prop_limit_properties_symmetry_limit_cutoff_localFinite M H omega N)
    hcutω φ hφ hunifφ mu hmu hmulf

end SubdiffusiveProcess.Paper
