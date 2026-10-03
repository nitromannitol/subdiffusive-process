module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.Support.LimitPropertiesSuppliers
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.DirichletForm.MeasureComparison

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped CompactlySupported ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Paper

def aux_lim_invariance_cutoff (d : ℕ) (n : ℕ) (x : SpatialCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (max 0 ((n : ℝ) - dist x 0)))

theorem aux_lim_invariance_cutoff_measurable {d : ℕ} (n : ℕ) :
    Measurable (aux_lim_invariance_cutoff d n) := by
  unfold aux_lim_invariance_cutoff
  fun_prop

theorem aux_lim_invariance_cutoff_mono {d : ℕ} {n m : ℕ} (hnm : n ≤ m) (x : SpatialCoordinates d) :
    aux_lim_invariance_cutoff d n x ≤ aux_lim_invariance_cutoff d m x := by
  unfold aux_lim_invariance_cutoff
  apply ENNReal.ofReal_mono
  apply min_le_min_left
  apply max_le_max_left
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  exact sub_le_sub_right hnm' _

theorem aux_lim_invariance_cutoff_le_one {d : ℕ} (n : ℕ) (x : SpatialCoordinates d) :
    aux_lim_invariance_cutoff d n x ≤ 1 := by
  unfold aux_lim_invariance_cutoff
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_mono (min_le_left _ _)

theorem aux_lim_invariance_cutoff_iSup {d : ℕ} (x : SpatialCoordinates d) :
    ⨆ n : ℕ, aux_lim_invariance_cutoff d n x = 1 := by
  apply le_antisymm
  · exact iSup_le fun n => aux_lim_invariance_cutoff_le_one n x
  · obtain ⟨n, hn⟩ := exists_nat_ge (dist x 0 + 1)
    have hdist : dist x 0 ≤ (n : ℝ) - 1 := by linarith
    have hmax : (1 : ℝ) ≤ max 0 ((n : ℝ) - dist x 0) :=
      le_max_of_le_right (by linarith)
    have hmin : (1 : ℝ) ≤ min 1 (max 0 ((n : ℝ) - dist x 0)) :=
      le_min le_rfl hmax
    have hc : (1 : ℝ≥0∞) ≤ aux_lim_invariance_cutoff d n x := by
      unfold aux_lim_invariance_cutoff
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_mono hmin
    exact le_trans hc (le_iSup (fun k : ℕ => aux_lim_invariance_cutoff d k x) n)

theorem aux_lim_invariance_of_symmetric
    {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (mu : Measure (SpatialCoordinates d))
    (hsym : SemigroupSymmetric P mu)
    (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, (∫⁻ y, f y ∂(P t x)) ∂mu = ∫⁻ x, f x ∂mu := by
  let g : ℕ → SpatialCoordinates d → ℝ≥0∞ := aux_lim_invariance_cutoff d
  have hg : ∀ n, Measurable (g n) := fun n => aux_lim_invariance_cutoff_measurable n
  have hgmono : ∀ n m, n ≤ m → ∀ x, g n x ≤ g m x := by
    intro n m hnm x
    exact aux_lim_invariance_cutoff_mono hnm x
  have hgi : ∀ x, ⨆ n, g n x = 1 := fun x => aux_lim_invariance_cutoff_iSup x
  have hleft_meas : ∀ n, Measurable (fun x => g n x * (∫⁻ y, f y ∂P t x)) := by
    intro n
    exact (hg n).mul hf.lintegral_kernel
  have hleft_mono : Monotone (fun n => fun x => g n x * (∫⁻ y, f y ∂P t x)) := by
    intro n m hnm x
    exact mul_le_mul_left (hgmono n m hnm x) _
  have hleft_iSup : (⨆ n, fun x => g n x * (∫⁻ y, f y ∂P t x)) =
      fun x => ∫⁻ y, f y ∂P t x := by
    funext x
    simp only [iSup_apply]
    rw [← ENNReal.iSup_mul, hgi x, one_mul]
  have hright_meas : ∀ n, Measurable (fun x => f x * (∫⁻ y, g n y ∂P t x)) := by
    intro n
    exact hf.mul (hg n).lintegral_kernel
  have hright_mono : Monotone (fun n => fun x => f x * (∫⁻ y, g n y ∂P t x)) := by
    intro n m hnm x
    exact mul_le_mul_right (lintegral_mono fun y => hgmono n m hnm y) _
  have hright_iSup : (⨆ n, fun x => f x * (∫⁻ y, g n y ∂P t x)) = f := by
    funext x
    simp only [iSup_apply]
    rw [← ENNReal.mul_iSup, ← lintegral_iSup (fun n => hg n) (hgmono)]
    have hgi_integral : (∫⁻ a, ⨆ n, g n a ∂P t x) = 1 := by
      simp_rw [hgi]
      rw [lintegral_one, hP t x]
    rw [hgi_integral, mul_one]
  have hsymn : ∀ n,
      (∫⁻ x, g n x * (∫⁻ y, f y ∂P t x) ∂mu) =
        ∫⁻ x, f x * (∫⁻ y, g n y ∂P t x) ∂mu := by
    intro n
    exact hsym t (g n) f (hg n) hf
  calc
    ∫⁻ x, (∫⁻ y, f y ∂P t x) ∂mu =
        ∫⁻ x, (⨆ n, g n x * (∫⁻ y, f y ∂P t x)) ∂mu := by
      simpa only [iSup_apply] using
        (congrArg (fun q : SpatialCoordinates d → ℝ≥0∞ => ∫⁻ x, q x ∂mu)
          hleft_iSup).symm
    _ = ⨆ n, ∫⁻ x, g n x * (∫⁻ y, f y ∂P t x) ∂mu :=
      lintegral_iSup hleft_meas hleft_mono
    _ = ⨆ n, ∫⁻ x, f x * (∫⁻ y, g n y ∂P t x) ∂mu := iSup_congr hsymn
    _ = ∫⁻ x, (⨆ n, f x * (∫⁻ y, g n y ∂P t x)) ∂mu :=
      (lintegral_iSup hright_meas hright_mono).symm
    _ = ∫⁻ x, f x ∂mu := by
      simpa only [iSup_apply] using
      congrArg (fun q : SpatialCoordinates d → ℝ≥0∞ => ∫⁻ x, q x ∂mu) hright_iSup

theorem aux_lim_invariance_continuous_limit
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (F : ℕ → BilateralField d → SpatialCoordinates d →
      ProbabilityMeasure (DiffusionPath d))
    (G : BilateralField d → SpatialCoordinates d →
      ProbabilityMeasure (DiffusionPath d))
    (hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
          pathLevyProkhorovDist (F N omega x) (G omega x) < epsilon)
    (hF : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N, Continuous (F N omega)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, Continuous (G omega) := by
  filter_upwards [hconv, hF] with omega hω hFω
  letI : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  have hFω' : ∀ N, Continuous (fun x =>
      LevyProkhorov.ofMeasure (F N omega x)) := by
    intro N
    exact LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp (hFω N)
  have hGω' : Continuous (fun x =>
      LevyProkhorov.ofMeasure (G omega x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hU : TendstoUniformlyOn
        (fun N y => LevyProkhorov.ofMeasure (F N omega y))
        (fun y => LevyProkhorov.ofMeasure (G omega y)) atTop
        (Metric.ball x 1) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro epsilon hepsilon
      obtain ⟨N0, hN0⟩ := hω (Metric.closedBall x 1)
        (isCompact_closedBall x 1) epsilon hepsilon
      filter_upwards [eventually_ge_atTop N0] with N hN y hy
      have hy' : y ∈ Metric.closedBall x 1 :=
        Metric.mem_closedBall.2 (Metric.mem_ball.1 hy).le
      have hb := hN0 N hN y hy'
      simp only [pathLevyProkhorovDist] at hb
      rw [dist_comm]
      exact hb
    exact (hU.continuousOn
      (Eventually.of_forall fun N => (hFω' N).continuousOn).frequently).continuousAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.comp hGω'

theorem aux_lim_invariance_localFinite_of_converges
    {d : ℕ}
    (muN : ℕ → Measure (SpatialCoordinates d))
    (mu0 mu : Measure (SpatialCoordinates d))
    (hmu0 : MeasuresConvergeLocally muN mu0)
    (hmu : MeasuresConvergeLocally muN mu)
    (hmu0local : IsLocallyFiniteMeasure mu0)
    (hmu0pos : mu0.IsOpenPosMeasure) :
    IsLocallyFiniteMeasure mu := by
  letI : IsLocallyFiniteMeasure mu0 := hmu0local
  letI : mu0.IsOpenPosMeasure := hmu0pos
  have heq : ∀ f : C_c(SpatialCoordinates d, ℝ),
      ∫ x, f x ∂mu = ∫ x, f x ∂mu0 := by
    intro f
    exact tendsto_nhds_unique (hmu f) (hmu0 f)
  refine ⟨fun x => ?_⟩
  obtain ⟨ϑ, hϑc, hϑsupp, hϑU, hϑnonneg, hϑle, hϑx⟩ :=
    DirichletForm.exists_continuous_plateau (isCompact_singleton)
      (Metric.isOpen_ball : IsOpen (Metric.ball x 1)) (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact Metric.mem_ball_self one_pos)
  have hϑint0 : Integrable ϑ mu0 := hϑc.integrable_of_hasCompactSupport hϑsupp
  let ϑc : C_c(SpatialCoordinates d, ℝ) := ⟨⟨ϑ, hϑc⟩, hϑsupp⟩
  have hϑpos0 : 0 < ∫ y, ϑ y ∂mu0 :=
    integral_pos_of_integrable_nonneg_nonzero hϑc hϑint0 hϑnonneg
      (by rw [hϑx x (Set.mem_singleton x)]; norm_num)
  have heqϑ : (∫ y, ϑ y ∂mu) = ∫ y, ϑ y ∂mu0 := by
    simpa [ϑc] using heq ϑc
  have hϑpos : 0 < ∫ y, ϑ y ∂mu := by
    calc
      0 < ∫ y, ϑ y ∂mu0 := hϑpos0
      _ = ∫ y, ϑ y ∂mu := heqϑ.symm
  have hϑint : Integrable ϑ mu := by
    by_contra hnot
    have hz : ∫ y, ϑ y ∂mu = 0 := integral_undef hnot
    linarith
  let U : Set (SpatialCoordinates d) := {y | (1 / 2 : ℝ) < ϑ y}
  have hU : IsOpen U := by
    exact hϑc.isOpen_preimage (Set.Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have hxU : x ∈ U := by
    change (1 / 2 : ℝ) < ϑ x
    rw [hϑx x (Set.mem_singleton x)]
    norm_num
  have hUle : mu U ≤ ENNReal.ofReal (∫ y, (2 : ℝ) * ϑ y ∂mu) := by
    apply Integrable.measure_le_integral (hϑint.const_mul 2)
      (Filter.Eventually.of_forall (fun y => mul_nonneg (by norm_num) (hϑnonneg y)))
    intro y hy
    change (1 / 2 : ℝ) < ϑ y at hy
    change (1 : ℝ) ≤ 2 * ϑ y
    exact (by linarith [hy])
  exact ⟨U, hU.mem_nhds hxU, lt_of_le_of_lt hUle ENNReal.ofReal_lt_top⟩

/-- The invariance clause of Theorem `lim:thm-measure` for the limiting process itself: for the
attached cutoff family and ANY kernel `K` that is, a.s., the locally uniform limit of `K_N` (the
convergence clause of `mfd_convergence`, which determines `K`), almost surely, for every local weak
limit `μ` of the cutoff speed measures, `∫ P_t f dμ = ∫ f dμ` with `P_t f(x) = ∫ f(Z_t) dK_x`. -/
theorem lim_invariance
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : Lane4.SobolevFoundationalInput d hd) (W : Lane4.SmallPerturbationInput d)
    (Cp : Lane4.CampanatoInput d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N))
        (hin : in_crossing M H PN KN)
        (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
          (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
        (hL : ∀ N omega x,
          Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
            L N omega x)
        (hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
            (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
        (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hK : IsMarkovKernel K)
        (hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ B : Set (SpatialCoordinates d), IsCompact B →
            ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
              pathLevyProkhorovDist
                (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                (jointPathProbabilityMeasure K hK omega x) < epsilon),
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ mu : Measure (SpatialCoordinates d),
            MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) mu →
            ∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
              ∫⁻ x, (∫⁻ w, f (w t) ∂(K (omega, x))) ∂mu = ∫⁻ x, f x ∂mu := by
  classical
  have heps : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  have hp : (d : ℝ) < (4 * d + 1 : ℕ) * (1 / 2 : ℝ) := by
    push_cast
    nlinarith
  obtain ⟨delta0, hdelta0, hgrowth⟩ := prop_chaos_growth hd (1 / 2 : ℝ) heps
    (4 * d + 1) hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It hM H hH PN KN hKN hin L hL hLloc K hK hconv
  obtain ⟨muFam, hmuFam, hmuFamAE, hmuFamGrowth⟩ := hgrowth M H hH hM
  have hcanonical : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFam omega) ∧
        IsLocallyFiniteMeasure (muFam omega) ∧
          (muFam omega).IsOpenPosMeasure := by
    filter_upwards [hmuFamAE] with omega hω
    refine ⟨?_, hω.2.1, hω.2.2.1⟩
    simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using hω.1
  have hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N, StrongMarkov (L N omega) := by
    filter_upwards [hLloc] with omega hω N
    exact (hω N).1
  have hlocal := tight_fixed_cutoff hd M H hH PN KN hKN hin L hL hLloc
  have hstartN := in_cutoff_start_continuity hd M H hH PN KN hKN hin hlocal
  have hKcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure K hK omega x) := by
    exact aux_lim_invariance_continuous_limit M
      (fun N omega x => jointPathProbabilityMeasure (KN N) (hKN N) omega x)
      (fun omega x => jointPathProbabilityMeasure K hK omega x) hconv hstartN
  have hrestartN := aux_limit_kernel_markov_passage_cutoff_restart hd M H PN KN hKN hin
  have hattachN := aux_limit_kernel_markov_passage_cutoff_attachment M H PN KN hin
  let κ : BilateralField d → Kernel (SpatialCoordinates d) (DiffusionPath d) := fun omega =>
    K.comap (Prod.mk omega) measurable_prodMk_left
  haveI hκ : ∀ omega, IsMarkovKernel (κ omega) := fun omega =>
    ⟨fun x => hK.isProbabilityMeasure (omega, x)⟩
  let Q : BilateralField d → Prop := fun omega =>
    (∀ x, (κ omega x).map (fun p => p 0) = Measure.dirac x) ∧
      (∀ x (t : ℝ≥0), (κ omega x).map (fun p => (p t, ContinuousPath.shift t p)) =
        ((κ omega x).map (fun p => p t)) ⊗ₘ κ omega)
  have hQ : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, Q omega := by
    filter_upwards [hKcont, hrestartN, hattachN.2, hconv] with omega hc hr ha hω
    let κs : ℕ → Kernel (SpatialCoordinates d) (DiffusionPath d) := fun N =>
      (KN N).comap (Prod.mk omega) measurable_prodMk_left
    haveI : ∀ N, IsMarkovKernel (κs N) := fun N =>
      ⟨fun x => (hKN N).isProbabilityMeasure (omega, x)⟩
    refine aux_limit_kernel_markov_passage_good κs (κ omega) hc ?_ ?_ ?_
    · intro B hB ε hε
      obtain ⟨N0, hN0⟩ := hω B hB ε hε
      filter_upwards [eventually_ge_atTop N0] with N hN y hy
      exact hN0 N hN y hy
    · intro N x
      have hmev : Measurable (ContinuousPath.finsetEvaluation
          (alpha := SpatialCoordinates d) ({0} : Finset ℝ≥0)) :=
        Measurable.of_eval fun t => (continuous_eval_const ((t : ℝ≥0))).measurable
      have h0 := map_eval_eq_of_finsetEvaluation (PN N omega) (KN N (omega, x)) x 0
        (by rw [← Kernel.map_apply _ hmev]; exact ha N {0} x)
      rw [(PN N omega).kernel_zero, Kernel.id_apply] at h0
      exact h0
    · intro N x t A hA F hF
      exact hr N x t A hA F hF
  let P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d) := fun omega =>
    if h : Q omega then
      aux_limit_kernel_markov_passage_marginalSemigroup (κ omega) h.1 h.2
    else idSemigroup
  have hP : ∀ omega, (P omega).IsConservative := by
    intro omega
    by_cases hω : Q omega
    · simp only [P, dif_pos hω]
      exact aux_limit_kernel_markov_passage_marginalSemigroup_isConservative _ _ _
    · simp only [P, dif_neg hω]
      exact isConservative_idSemigroup
  have hlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x := by
    filter_upwards [hQ] with omega hω I x
    simp only [P, dif_pos hω]
    have hmev : Measurable (ContinuousPath.finsetEvaluation
        (alpha := SpatialCoordinates d) I) :=
      Measurable.of_eval fun t => (continuous_eval_const ((t : ℝ≥0))).measurable
    rw [Kernel.map_apply _ hmev]
    exact aux_limit_kernel_markov_passage_map_finsetEvaluation (κ omega) hω.1 hω.2 I x
  have hcutoff : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N, SemigroupSymmetric (PN N omega) (cutoffSpeedMeasure M H omega N) :=
    prop_limit_properties_cutoff_symmetry M H PN KN hin L hL hLloc hLstrong
  have hsym : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ mu : Measure (SpatialCoordinates d),
        MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) mu →
        SemigroupSymmetric (P omega) mu := by
    filter_upwards [hQ, hKcont, hstartN, hcutoff, hin.2.2, hconv, hlim, hcanonical]
      with omega hQω hKω hNω hcutω hattω hconvω hlimω hcan
    intro mu hmu
    have hμlocal := aux_lim_invariance_localFinite_of_converges
      (fun N => cutoffSpeedMeasure M H omega N) (muFam omega) mu
      hcan.1 hmu hcan.2.1 hcan.2.2
    exact aux_prop_limit_properties_symmetry_limit_fixed KN hKN K hK
      (fun N => PN N omega) (P omega) omega hlimω
      (fun N I x => hattω N I x) hNω hKω
      (fun N => cutoffSpeedMeasure M H omega N)
      (fun N => by
        simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using
          weightedChaosCutoff_isLocallyFinite M H N omega)
      hcutω (fun j => j) tendsto_id (by
        intro B hB eps heps
        obtain ⟨N0, hN0⟩ := hconvω B hB eps heps
        exact ⟨N0, fun j hj x hx => hN0 j hj x hx⟩) mu hmu hμlocal
  filter_upwards [hsym, hQ, hKcont, hlim] with omega hsymω hQω hKω hlimω
  intro mu hmu t f hf
  have hinv := aux_lim_invariance_of_symmetric (P omega) (hP omega) mu
    (hsymω mu hmu) t f hf
  have hmap : ∀ x : SpatialCoordinates d,
      (K (omega, x)).map (fun w : DiffusionPath d => w t) = P omega t x := by
    intro x
    apply SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation (P omega) (K (omega, x)) x t
    rw [← Kernel.map_apply K (ContinuousPath.measurable_finsetEvaluation _)]
    exact hlimω ({t} : Finset ℝ≥0) x
  have hinner : ∀ x : SpatialCoordinates d,
      ∫⁻ y, f y ∂P omega t x =
        ∫⁻ w, f (w t) ∂K (omega, x) := by
    intro x
    rw [← hmap x, lintegral_map]
    · exact hf
    · exact (continuous_eval_const t).measurable
  calc
    ∫⁻ x, (∫⁻ w, f (w t) ∂K (omega, x)) ∂mu =
        ∫⁻ x, (∫⁻ y, f y ∂P omega t x) ∂mu := by
      congr 1
      funext x
      exact (hinner x).symm
    _ = ∫⁻ x, f x ∂mu := hinv

end Paper

