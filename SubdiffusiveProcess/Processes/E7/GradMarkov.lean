import SubdiffusiveProcess.Processes.E7.GradForm
import SubdiffusiveProcess.Sobolev.UniformSmoothSources

/-!
# The Markov property and regularity of the gradient form

Smooth contractions and the unit truncation operate on `E`; the smooth compactly supported functions
form a core. Everything is proved by dominated convergence along a.e.-convergent subsequences of
approximating test functions, using only that the graph is closed.
-/
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- The `L²(ρ)` class of a test function. -/
def tcls {ρ : St d → ℝ} (hρ : Continuous ρ) (φ : St d → ℝ) (hφ : φ ∈ testFns d) :
    Lp ℝ 2 (wm ρ) := (memLp_wm_of_test hρ hφ).toLp φ

/-- The `L²(c)` class of a partial derivative of a test function. -/
def gcls {c : St d → ℝ} (hc : Continuous c) (φ : St d → ℝ) (hφ : φ ∈ testFns d) (i : Fin d) :
    Lp ℝ 2 (wm c) := (memLp_wm_dpartial hc hφ i).toLp (dpartial i φ)

theorem test_mem_gradGraph {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    {φ : St d → ℝ} (hφ : φ ∈ testFns d) :
    (tcls hρ φ hφ, fun i => gcls hc φ hφ i) ∈ gradGraph hc hρ := by
  have h : testToG hc hρ ⟨φ, hφ⟩ = (tcls hρ φ hφ, fun i => gcls hc φ hφ i) := rfl
  rw [← h]
  exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (testToGLin hc hρ) ⟨φ, hφ⟩)

theorem tcls_mem_gradDomain {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    {φ : St d → ℝ} (hφ : φ ∈ testFns d) : tcls hρ φ hφ ∈ gradDomain hc hρ := by
  exact (mem_gradDomain_iff hc hρ _).2 ⟨_, test_mem_gradGraph hc hρ hφ⟩

theorem gradOf_tcls {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {φ : St d → ℝ} (hφ : φ ∈ testFns d) :
    gradOf hc hρ (tcls hρ φ hφ) = fun i => gcls hc φ hφ i := by
  exact gradOf_spec hc hρ hcpos hρpos (test_mem_gradGraph hc hρ hφ)

/-- Every domain element is the limit of a sequence of test functions whose gradients converge to
its gradient. -/
theorem exists_test_sequence {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {u : Lp ℝ 2 (wm ρ)}
    (hu : u ∈ gradDomain hc hρ) :
    ∃ (φ : ℕ → St d → ℝ) (hφ : ∀ n, φ n ∈ testFns d),
      Tendsto (fun n => tcls hρ (φ n) (hφ n)) atTop (𝓝 u) ∧
      ∀ i, Tendsto (fun n => gcls hc (φ n) (hφ n) i) atTop (𝓝 (gradOf hc hρ u i)) := by
  rw [mem_gradDomain_iff hc hρ] at hu
  obtain ⟨g, hg⟩ := hu
  have hg_eq : gradOf hc hρ u = g := gradOf_spec hc hρ hcpos hρpos hg
  have h_closure : (u, g) ∈ closure (LinearMap.range (testToGLin hc hρ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hg
  rw [mem_closure_iff_seq_limit] at h_closure
  obtain ⟨z, hz_range, hz_limit⟩ := h_closure
  have h_range : ∀ n, ∃ ψ : testFns d, z n = testToGLin hc hρ ψ := fun n => by
    obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp (hz_range n)
    exact ⟨ψ, hψ.symm⟩
  choose ψ hψ using h_range
  use fun n => ψ n, fun n => (ψ n).2
  constructor
  · have h1 : Tendsto (fun n => (z n).1) atTop (𝓝 u) := by
      exact (continuous_fst.tendsto (u, g)).comp hz_limit
    convert h1 using 2
    ext n
    rw [hψ]
    rfl
  · intro i
    have h2 : Tendsto (fun n => (z n).2 i) atTop (𝓝 (g i)) := by
      have : Tendsto (fun n => (z n).2) atTop (𝓝 g) := by
        exact (continuous_snd.tendsto (u, g)).comp hz_limit
      exact (continuous_apply i).continuousAt.tendsto.comp this
    convert h2 using 2
    · ext n
      rw [hψ]
      rfl
    · rw [hg_eq]

/-- Conversely, limits of such sequences are graph points. -/
theorem mem_gradGraph_of_tendsto {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    {u : Lp ℝ 2 (wm ρ)} {g : Fin d → Lp ℝ 2 (wm c)} (φ : ℕ → St d → ℝ)
    (hφ : ∀ n, φ n ∈ testFns d)
    (h1 : Tendsto (fun n => tcls hρ (φ n) (hφ n)) atTop (𝓝 u))
    (h2 : ∀ i, Tendsto (fun n => gcls hc (φ n) (hφ n) i) atTop (𝓝 (g i))) :
    (u, g) ∈ gradGraph hc hρ := by
  have hclosed := isClosed_gradGraph hc hρ
  have htend : Tendsto (fun n => (tcls hρ (φ n) (hφ n), fun i => gcls hc (φ n) (hφ n) i))
      atTop (𝓝 (u, g)) :=
    Filter.Tendsto.prodMk_nhds h1 (tendsto_pi_nhds.2 h2)
  have heventually : ∀ᶠ n in atTop, (tcls hρ (φ n) (hφ n), fun i => gcls hc (φ n) (hφ n) i) ∈ gradGraph hc hρ :=
    Eventually.of_forall fun n => test_mem_gradGraph hc hρ (hφ n)
  exact hclosed.mem_of_tendsto htend heventually

/-- The energy-norm distance of `u` to a test function is the sum of the two squared distances. -/
theorem energyNormSq_sub_test {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {u : Lp ℝ 2 (wm ρ)}
    (hu : u ∈ gradDomain hc hρ) {φ : St d → ℝ} (hφ : φ ∈ testFns d) :
    (gradClosedForm hc hρ hcpos hρpos).energyNormSq (u - tcls hρ φ hφ) =
      ∑ i, ‖gradOf hc hρ u i - gcls hc φ hφ i‖ ^ 2 + ‖u - tcls hρ φ hφ‖ ^ 2 := by
  unfold DirichletForm.ClosedForm.energyNormSq
  simp only [gradClosedForm]
  rw [gradForm_self hc hρ (u - tcls hρ φ hφ)]
  have h_tcls : tcls hρ φ hφ ∈ gradDomain hc hρ := tcls_mem_gradDomain hc hρ hφ
  rw [gradOf_sub hc hρ hcpos hρpos hu h_tcls]
  rw [gradOf_tcls hc hρ hcpos hρpos hφ]
  simp only [Pi.sub_apply]

/-- Dominated convergence in `L²`. -/
theorem tendsto_eLpNorm_two_of_dominated {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f G : α → ℝ} (hG : MemLp G 2 μ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hb : ∀ n, ∀ᵐ x ∂μ, |F n x| ≤ G x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => eLpNorm (fun x => F n x - f x) 2 μ) atTop (𝓝 0) := by
  have hfm : AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae atTop hF hlim
  have hfG : ∀ᵐ x ∂μ, |f x| ≤ G x := by
    filter_upwards [ae_all_iff.2 hb, hlim] with x hx hl
    exact le_of_tendsto' hl.abs (fun n => hx n)
  have hnorm : ∀ n, eLpNorm (fun x => F n x - f x) 2 μ =
      (∫⁻ x, ‖F n x - f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    simp
  have hG2 : ∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
    have h := hG.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)] at h
    intro htop
    simp only [ENNReal.toReal_ofNat, htop] at h
    simp at h
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x - f x‖ₑ ^ (2 : ℝ) ≤ 4 * ‖G x‖ₑ ^ (2 : ℝ) := by
    intro n
    filter_upwards [hb n, hfG] with x h1 h2
    have hG0 : 0 ≤ G x := le_trans (abs_nonneg _) h1
    have h3 : ‖F n x - f x‖ₑ ≤ 2 * ‖G x‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_eq_abs, Real.norm_eq_abs,
        show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc |F n x - f x| ≤ |F n x| + |f x| := abs_sub _ _
        _ ≤ 2 * |G x| := by rw [abs_of_nonneg hG0]; linarith
    calc ‖F n x - f x‖ₑ ^ (2 : ℝ) ≤ (2 * ‖G x‖ₑ) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h3 (by norm_num)
      _ = 4 * ‖G x‖ₑ ^ (2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          congr 1
          rw [show (2 : ℝ≥0∞) ^ (2 : ℝ) = 4 by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num]
  have hmain : Tendsto (fun n => ∫⁻ x, ‖F n x - f x‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have hint : ∫⁻ x, 4 * ‖G x‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
      rw [lintegral_const_mul' _ _ (by norm_num)]
      exact ENNReal.mul_ne_top (by norm_num) hG2
    have := tendsto_lintegral_of_dominated_convergence'
      (μ := μ) (F := fun n x => ‖F n x - f x‖ₑ ^ (2 : ℝ)) (f := fun _ => (0 : ℝ≥0∞))
      (fun x => 4 * ‖G x‖ₑ ^ (2 : ℝ))
      (fun n => ((hF n).sub hfm).enorm.pow_const _) hbound hint ?_
    · simpa using this
    · filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun n => ‖F n x - f x‖ₑ) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n => ‖F n x - f x‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.1 hx
        have := ENNReal.tendsto_ofReal h0
        rw [ENNReal.ofReal_zero] at this
        exact this.congr fun n => ofReal_norm_eq_enorm _
      have := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0 |>.comp h1
      simpa using this
  have hfinal := (ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ)))).tendsto 0 |>.comp hmain
  simp only [hnorm]
  simpa using hfinal

/-- A convergent sequence of test-function classes has an a.e.-convergent subsequence of
representatives, still with converging gradients. -/
theorem exists_ae_test_sequence {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {u : Lp ℝ 2 (wm ρ)}
    (hu : u ∈ gradDomain hc hρ) :
    ∃ (φ : ℕ → St d → ℝ) (hφ : ∀ n, φ n ∈ testFns d),
      Tendsto (fun n => tcls hρ (φ n) (hφ n)) atTop (𝓝 u) ∧
      (∀ i, Tendsto (fun n => gcls hc (φ n) (hφ n) i) atTop (𝓝 (gradOf hc hρ u i))) ∧
      ∀ᵐ x ∂(wm ρ), Tendsto (fun n => φ n x) atTop (𝓝 (u x)) := by
  obtain ⟨φ, hφ, h1, h2⟩ := exists_test_sequence hc hρ hcpos hρpos hu
  have hmeasf : ∀ n, AEStronglyMeasurable (⇑(tcls hρ (φ n) (hφ n))) (wm ρ) :=
    fun n => (Lp.stronglyMeasurable _).aestronglyMeasurable
  have hin : TendstoInMeasure (wm ρ) (fun n => ⇑(tcls hρ (φ n) (hφ n))) atTop ⇑u := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hmeasf
      (Lp.stronglyMeasurable u).aestronglyMeasurable ?_
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 h1
  obtain ⟨ns, hns, hae⟩ := hin.exists_seq_tendsto_ae
  refine ⟨fun k => φ (ns k), fun k => hφ (ns k), h1.comp hns.tendsto_atTop,
    fun i => (h2 i).comp hns.tendsto_atTop, ?_⟩
  have hrep : ∀ᵐ x ∂(wm ρ), ∀ n, ⇑(tcls hρ (φ n) (hφ n)) x = φ n x :=
    ae_all_iff.2 fun n => MemLp.coeFn_toLp _
  filter_upwards [hae, hrep] with x hx hr
  simp only [hr] at hx
  exact hx

/-- Composition of a test function with a smooth function vanishing at zero. -/
theorem comp_mem_testFns {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (h0 : Ψ 0 = 0)
    {φ : St d → ℝ} (hφ : φ ∈ testFns d) : (fun x => Ψ (φ x)) ∈ testFns d := by
  constructor
  · exact hΨ.comp hφ.1
  · exact HasCompactSupport.comp_left hφ.2 h0

theorem dpartial_comp {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {φ : St d → ℝ}
    (hφ : φ ∈ testFns d) (i : Fin d) :
    dpartial i (fun x => Ψ (φ x)) = fun x => deriv Ψ (φ x) * dpartial i φ x := by
  funext x
  have hφd : DifferentiableAt ℝ φ x := (hφ.1.differentiable (by decide)).differentiableAt
  have hΨd : DifferentiableAt ℝ Ψ (φ x) := (hΨ.differentiable (by decide)).differentiableAt
  have h1 : HasFDerivAt (fun x => Ψ (φ x)) (deriv Ψ (φ x) • fderiv ℝ φ x) x :=
    hΨd.hasDerivAt.comp_hasFDerivAt x hφd.hasFDerivAt
  unfold dpartial
  rw [h1.fderiv]
  simp

theorem abs_sub_le_of_deriv_le {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hb : ∀ t, |deriv Ψ t| ≤ 1) (s t : ℝ) : |Ψ s - Ψ t| ≤ |s - t| := by
  have h_univ : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  have h_diff : ∀ x ∈ Set.univ, DifferentiableAt ℝ Ψ x := fun x _ =>
    (hΨ.differentiable (by decide)).differentiableAt
  have h_deriv_norm : ∀ x ∈ Set.univ, ‖deriv Ψ x‖ ≤ 1 := fun x _ => by
    rw [Real.norm_eq_abs]
    exact hb x
  have h := Convex.norm_image_sub_le_of_norm_deriv_le h_diff h_deriv_norm h_univ
    (Set.mem_univ t) (Set.mem_univ s)
  simp only [Real.norm_eq_abs, one_mul, abs_sub_comm] at h ⊢
  exact h

/-- The derivative of the `k`-th smooth clamp: a smooth bump equal to one on
`[1/(k+2), 1 - 1/(k+2)]` and zero outside `(0, 1)`. -/
def smoothClampDeriv (k : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition (t * ((k : ℝ) + 2)) * Real.smoothTransition ((1 - t) * ((k : ℝ) + 2))

/-- The `k`-th smooth clamp, the integral of the bump. -/
def smoothClamp (k : ℕ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, smoothClampDeriv k s

theorem smoothClampDeriv_contDiff (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smoothClampDeriv k) := by
  unfold smoothClampDeriv
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.mul contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).mul contDiff_const))

theorem smoothClampDeriv_mem_Icc (k : ℕ) (t : ℝ) :
    0 ≤ smoothClampDeriv k t ∧ smoothClampDeriv k t ≤ 1 := by
  unfold smoothClampDeriv
  constructor
  · apply mul_nonneg
    · exact Real.smoothTransition.nonneg _
    · exact Real.smoothTransition.nonneg _
  · apply mul_le_one₀
    · exact Real.smoothTransition.le_one _
    · exact Real.smoothTransition.nonneg _
    · exact Real.smoothTransition.le_one _

theorem smoothClamp_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (smoothClamp k) (smoothClampDeriv k t) t := by
  have hcont := (smoothClampDeriv_contDiff k).continuous
  exact (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem smoothClamp_contDiff (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smoothClamp k) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (smoothClamp_hasDerivAt k x).differentiableAt, ?_⟩
  have : deriv (smoothClamp k) = smoothClampDeriv k := by
    ext x
    exact (smoothClamp_hasDerivAt k x).deriv
  rw [this]
  exact smoothClampDeriv_contDiff k

theorem smoothClamp_zero (k : ℕ) : smoothClamp k 0 = 0 := by
  unfold smoothClamp
  exact intervalIntegral.integral_same

theorem deriv_smoothClamp (k : ℕ) (t : ℝ) : deriv (smoothClamp k) t = smoothClampDeriv k t :=
  (smoothClamp_hasDerivAt k t).deriv

theorem abs_smoothClamp_le (k : ℕ) (t : ℝ) : |smoothClamp k t| ≤ |t| := by
  unfold smoothClamp
  have h : ∀ x ∈ Set.uIoc 0 t, ‖smoothClampDeriv k x‖ ≤ 1 := fun x _ => by
    have ⟨h0, h1⟩ := smoothClampDeriv_mem_Icc k x
    norm_num [abs_of_nonneg h0] at *
    exact h1
  have := intervalIntegral.norm_integral_le_of_norm_le_const h
  simp only at this ⊢
  norm_num at this ⊢
  exact this

theorem smoothClampDeriv_tendsto (t : ℝ) :
    Tendsto (fun k => smoothClampDeriv k t) atTop
      (𝓝 (Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) t)) := by
  unfold smoothClampDeriv
  by_cases h0 : t ≤ 0
  · have hz : ∀ k : ℕ, Real.smoothTransition (t * ((k : ℝ) + 2)) = 0 := fun k =>
      Real.smoothTransition.zero_of_nonpos (by nlinarith [(by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)])
    have hn : t ∉ Ioo (0 : ℝ) 1 := fun h => by linarith [h.1]
    simp_rw [hz, zero_mul]
    rw [Set.indicator_of_notMem hn]
    exact tendsto_const_nhds
  · by_cases h1 : 1 ≤ t
    · have hz : ∀ k : ℕ, Real.smoothTransition ((1 - t) * ((k : ℝ) + 2)) = 0 := fun k =>
        Real.smoothTransition.zero_of_nonpos
          (by nlinarith [(by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)])
      have hn : t ∉ Ioo (0 : ℝ) 1 := fun h => by linarith [h.2]
      simp_rw [hz, mul_zero]
      rw [Set.indicator_of_notMem hn]
      exact tendsto_const_nhds
    · push_neg at h0 h1
      have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
      rw [Set.indicator_of_mem ht]
      obtain ⟨N1, hN1⟩ := exists_nat_gt (1 / t)
      obtain ⟨N2, hN2⟩ := exists_nat_gt (1 / (1 - t))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (max N1 N2)] with k hk
      have hk1 : (N1 : ℝ) ≤ k := by exact_mod_cast le_trans (le_max_left _ _) hk
      have hk2 : (N2 : ℝ) ≤ k := by exact_mod_cast le_trans (le_max_right _ _) hk
      have h1t : 0 < 1 - t := by linarith
      have e1 : 1 ≤ t * ((k : ℝ) + 2) := by
        have : 1 / t < (k : ℝ) + 2 := by linarith
        rw [div_lt_iff₀ h0] at this
        linarith
      have e2 : 1 ≤ (1 - t) * ((k : ℝ) + 2) := by
        have : 1 / (1 - t) < (k : ℝ) + 2 := by linarith
        rw [div_lt_iff₀ h1t] at this
        linarith
      rw [Real.smoothTransition.one_of_one_le e1, Real.smoothTransition.one_of_one_le e2, mul_one]

theorem integral_indicator_Ioo_zero_one (t : ℝ) :
    ∫ s in (0 : ℝ)..t, Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) s =
      DirichletForm.unitTruncation t := by
  unfold DirichletForm.unitTruncation
  rcases le_or_gt 0 t with ht | ht
  · rw [intervalIntegral.integral_of_le ht, setIntegral_indicator measurableSet_Ioo,
      setIntegral_const, smul_eq_mul, mul_one]
    rcases lt_or_ge t 1 with h1 | h1
    · have : Ioc 0 t ∩ Ioo 0 1 = Ioc 0 t :=
        Set.inter_eq_left.mpr (fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 h1⟩)
      rw [this, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      rw [min_eq_left h1.le, max_eq_left ht]
      ring
    · have : Ioc 0 t ∩ Ioo 0 1 = Ioo 0 1 :=
        Set.inter_eq_right.mpr (fun s hs => ⟨hs.1, by linarith [hs.2]⟩)
      rw [this, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by norm_num)]
      rw [min_eq_right h1, max_eq_left (by norm_num)]
      norm_num
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le ht.le,
      setIntegral_indicator measurableSet_Ioo]
    have : Ioc t 0 ∩ Ioo 0 1 = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, h2⟩, h3, _⟩
      linarith
    rw [this]
    simp only [Measure.restrict_empty, integral_zero_measure, neg_zero]
    rw [min_eq_left (by linarith), max_eq_right ht.le]

theorem smoothClamp_tendsto (t : ℝ) :
    Tendsto (fun k => smoothClamp k t) atTop (𝓝 (DirichletForm.unitTruncation t)) := by
  unfold smoothClamp
  rw [← integral_indicator_Ioo_zero_one t]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall fun k =>
      (smoothClampDeriv_contDiff k).continuous.aestronglyMeasurable
  · refine Eventually.of_forall fun k => Eventually.of_forall fun x _ => ?_
    have h := smoothClampDeriv_mem_Icc k x
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  · exact Eventually.of_forall fun x _ => smoothClampDeriv_tendsto x

/-! ### Smooth contractions and the unit truncation operate -/

theorem memLp_comp_wm {ρ : St d → ℝ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (h0 : Ψ 0 = 0)
    (hb : ∀ t, |deriv Ψ t| ≤ 1) (u : Lp ℝ 2 (wm ρ)) : MemLp (fun x => Ψ (u x)) 2 (wm ρ) := by
  have lip : LipschitzWith 1 Ψ :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq]
      norm_cast
      have h := abs_sub_le_of_deriv_le hΨ hb x y
      linarith
  exact LipschitzWith.comp_memLp lip h0 (Lp.memLp u)

theorem memLp_mul_deriv_wm {c ρ : St d → ℝ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hb : ∀ t, |deriv Ψ t| ≤ 1) (u : Lp ℝ 2 (wm ρ)) (g : Lp ℝ 2 (wm c)) :
    MemLp (fun x => deriv Ψ (u x) * g x) 2 (wm c) := by
  -- Measurability: deriv Ψ is continuous, u is strongly measurable, so their composition is
  have hu_meas : StronglyMeasurable ⇑u := Lp.stronglyMeasurable u
  have hderiv_cont : Continuous (deriv Ψ) := hΨ.continuous_deriv (by trivial)
  have hderiv_u_meas : StronglyMeasurable (fun x => deriv Ψ (u x)) :=
    hderiv_cont.comp_stronglyMeasurable hu_meas
  have hg_meas : StronglyMeasurable ⇑g := Lp.stronglyMeasurable g
  have hmeas : AEStronglyMeasurable (fun x => deriv Ψ (u x) * g x) (wm c) :=
    (hderiv_u_meas.mul hg_meas).aestronglyMeasurable

  -- Domination: |deriv Ψ (u x)| ≤ 1, so |deriv Ψ (u x) * g x| ≤ |g x|
  have hle : ∀ᵐ x ∂(wm c), ‖deriv Ψ (u x) * g x‖ ≤ ‖g x‖ := by
    filter_upwards with x
    simp only [norm_mul]
    have h1 : |deriv Ψ (u x)| ≤ 1 := hb (u x)
    have h2 : ‖deriv Ψ (u x)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact h1
    calc ‖deriv Ψ (u x)‖ * ‖g x‖ ≤ 1 * ‖g x‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ‖g x‖ := one_mul _

  -- Apply MemLp.of_le
  exact MemLp.of_le (Lp.memLp g) hmeas hle

theorem tendsto_eLpNorm_tcls {ρ : St d → ℝ} (hρ : Continuous ρ) {u : Lp ℝ 2 (wm ρ)}
    {φ : ℕ → St d → ℝ} {hφ : ∀ n, φ n ∈ testFns d}
    (h1 : Tendsto (fun n => tcls hρ (φ n) (hφ n)) atTop (𝓝 u)) :
    Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (wm ρ)) atTop (𝓝 0) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h1
  refine h1.congr fun n => ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_wm_of_test hρ (hφ n))] with x hx
  simp only [tcls, Pi.sub_apply, hx]

theorem tendsto_eLpNorm_gcls {c : St d → ℝ} (hc : Continuous c) {g : Lp ℝ 2 (wm c)}
    {φ : ℕ → St d → ℝ} {hφ : ∀ n, φ n ∈ testFns d} {i : Fin d}
    (h2 : Tendsto (fun n => gcls hc (φ n) (hφ n) i) atTop (𝓝 g)) :
    Tendsto (fun n => eLpNorm (fun x => dpartial i (φ n) x - g x) 2 (wm c)) atTop (𝓝 0) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h2
  refine h2.congr fun n => ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_wm_dpartial hc (hφ n) i)] with x hx
  simp only [gcls, Pi.sub_apply, hx]

/-- The composed test functions converge to the composition, in `L²(ρ)`. -/
theorem tendsto_comp_eLpNorm {ρ : St d → ℝ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hb : ∀ t, |deriv Ψ t| ≤ 1) {u : Lp ℝ 2 (wm ρ)} {φ : ℕ → St d → ℝ}
    (h : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (wm ρ)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Ψ (φ n x) - Ψ (u x)) 2 (wm ρ)) atTop (𝓝 0) := by
  have pointwise : ∀ n x, |Ψ (φ n x) - Ψ (u x)| ≤ |φ n x - u x| := fun n x =>
    abs_sub_le_of_deriv_le hΨ hb (φ n x) (u x)
  have le : ∀ n, eLpNorm (fun x => Ψ (φ n x) - Ψ (u x)) 2 (wm ρ) ≤
            eLpNorm (fun x => φ n x - u x) 2 (wm ρ) := fun n => by
    refine eLpNorm_mono ?_
    intro x
    show ‖Ψ (φ n x) - Ψ (u x)‖ ≤ ‖φ n x - u x‖
    exact_mod_cast pointwise n x
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le _) le

/-- The chain-rule gradients of the composed test functions converge in `L²(c)`. -/
theorem tendsto_grad_comp_eLpNorm {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hb : ∀ t, |deriv Ψ t| ≤ 1) {u : Lp ℝ 2 (wm ρ)}
    {φ : ℕ → St d → ℝ} (hφ : ∀ n, φ n ∈ testFns d) {g : Lp ℝ 2 (wm c)} {i : Fin d}
    (hgrad : Tendsto (fun n => eLpNorm (fun x => dpartial i (φ n) x - g x) 2 (wm c)) atTop
      (𝓝 0))
    (hae : ∀ᵐ x ∂(wm ρ), Tendsto (fun n => φ n x) atTop (𝓝 (u x))) :
    Tendsto (fun n => eLpNorm (fun x => deriv Ψ (φ n x) * dpartial i (φ n) x -
      deriv Ψ (u x) * g x) 2 (wm c)) atTop (𝓝 0) := by
  have hcontD : Continuous (deriv Ψ) := hΨ.continuous_deriv (by decide)
  have hφm : ∀ n, StronglyMeasurable (φ n) := fun n => (hφ n).1.continuous.stronglyMeasurable
  have hdφm : ∀ n, StronglyMeasurable (dpartial i (φ n)) := fun n =>
    (dpartial_mem_test_cont (hφ n) i).stronglyMeasurable
  have hum : StronglyMeasurable ⇑u := Lp.stronglyMeasurable u
  have hgm : StronglyMeasurable ⇑g := Lp.stronglyMeasurable g
  have hdecomp : ∀ n x, deriv Ψ (φ n x) * dpartial i (φ n) x - deriv Ψ (u x) * g x =
      deriv Ψ (φ n x) * (dpartial i (φ n) x - g x) +
        (deriv Ψ (φ n x) - deriv Ψ (u x)) * g x := fun n x => by ring
  have hm1 : ∀ n, AEStronglyMeasurable
      (fun x => deriv Ψ (φ n x) * (dpartial i (φ n) x - g x)) (wm c) := fun n =>
    (((hcontD.comp_stronglyMeasurable (hφm n)).mul ((hdφm n).sub hgm))).aestronglyMeasurable
  have hm2 : ∀ n, AEStronglyMeasurable
      (fun x => (deriv Ψ (φ n x) - deriv Ψ (u x)) * g x) (wm c) := fun n =>
    ((((hcontD.comp_stronglyMeasurable (hφm n)).sub
      (hcontD.comp_stronglyMeasurable hum)).mul hgm)).aestronglyMeasurable
  have hb1 : ∀ n, eLpNorm (fun x => deriv Ψ (φ n x) * (dpartial i (φ n) x - g x)) 2 (wm c) ≤
      eLpNorm (fun x => dpartial i (φ n) x - g x) 2 (wm c) := fun n => by
    refine eLpNorm_mono fun x => ?_
    simp only [norm_mul]
    calc ‖deriv Ψ (φ n x)‖ * ‖dpartial i (φ n) x - g x‖ ≤ 1 * ‖dpartial i (φ n) x - g x‖ :=
          mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hb _) (norm_nonneg _)
      _ = _ := one_mul _
  -- the second term tends to zero by dominated convergence
  have hae' : ∀ᵐ x ∂(wm c), Tendsto (fun n => φ n x) atTop (𝓝 (u x)) :=
    ae_wm_of_ae_volume hc hcpos (ae_volume_of_ae_wm hρ hρpos hae)
  have h2 : Tendsto (fun n => eLpNorm (fun x => (deriv Ψ (φ n x) - deriv Ψ (u x)) * g x) 2
      (wm c)) atTop (𝓝 0) := by
    have := tendsto_eLpNorm_two_of_dominated
      (F := fun n x => (deriv Ψ (φ n x) - deriv Ψ (u x)) * g x) (f := fun _ => (0 : ℝ))
      (G := fun x => 2 * ‖g x‖) ((Lp.memLp g).norm.const_mul 2) hm2 ?_ ?_
    · simpa using this
    · intro n
      filter_upwards with x
      have h1 := hb (φ n x)
      have h2 := hb (u x)
      have hle : |deriv Ψ (φ n x) - deriv Ψ (u x)| ≤ 2 := by
        have := abs_sub (deriv Ψ (φ n x)) (deriv Ψ (u x))
        linarith
      rw [abs_mul, ← Real.norm_eq_abs (g x)]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    · filter_upwards [hae'] with x hx
      have h3 : Tendsto (fun n => deriv Ψ (φ n x)) atTop (𝓝 (deriv Ψ (u x))) :=
        (hcontD.tendsto _).comp hx
      have := (h3.sub_const (deriv Ψ (u x))).mul_const (g x)
      simpa using this
  have hsum : ∀ n, eLpNorm (fun x => deriv Ψ (φ n x) * dpartial i (φ n) x -
      deriv Ψ (u x) * g x) 2 (wm c) ≤
      eLpNorm (fun x => dpartial i (φ n) x - g x) 2 (wm c) +
        eLpNorm (fun x => (deriv Ψ (φ n x) - deriv Ψ (u x)) * g x) 2 (wm c) := fun n => by
    have hfun : (fun x => deriv Ψ (φ n x) * dpartial i (φ n) x - deriv Ψ (u x) * g x) =
        (fun x => deriv Ψ (φ n x) * (dpartial i (φ n) x - g x)) +
          (fun x => (deriv Ψ (φ n x) - deriv Ψ (u x)) * g x) := by
      funext x
      exact hdecomp n x
    rw [hfun]
    exact (eLpNorm_add_le (hm1 n) (hm2 n) (by norm_num)).trans
      (add_le_add (hb1 n) le_rfl)
  have hlim := hgrad.add h2
  rw [add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le _) hsum

/-- A smooth contraction vanishing at zero composes with a domain element, with the chain-rule
gradient. -/
theorem compose_smooth_mem {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (h0 : Ψ 0 = 0) (hb : ∀ t, |deriv Ψ t| ≤ 1)
    {u : Lp ℝ 2 (wm ρ)} (hu : u ∈ gradDomain hc hρ) :
    ∃ v : Lp ℝ 2 (wm ρ), v ∈ gradDomain hc hρ ∧ (⇑v =ᵐ[wm ρ] fun x => Ψ (u x)) ∧
      ∀ i, ⇑(gradOf hc hρ v i) =ᵐ[wm c] fun x => deriv Ψ (u x) * gradOf hc hρ u i x := by
  obtain ⟨φ, hφ, h1, h2, h3⟩ := exists_ae_test_sequence hc hρ hcpos hρpos hu
  have hcomp : ∀ n, (fun x => Ψ (φ n x)) ∈ testFns d := fun n => comp_mem_testFns hΨ h0 (hφ n)
  have hΨu := memLp_comp_wm hΨ h0 hb u
  have hmg := fun i => memLp_mul_deriv_wm (c := c) hΨ hb u (gradOf hc hρ u i)
  have hv : Tendsto (fun n => tcls hρ (fun x => Ψ (φ n x)) (hcomp n)) atTop
      (𝓝 (hΨu.toLp (fun x => Ψ (u x)))) := by
    unfold tcls
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    exact tendsto_comp_eLpNorm hΨ hb (tendsto_eLpNorm_tcls hρ h1)
  have hh : ∀ i, Tendsto (fun n => gcls hc (fun x => Ψ (φ n x)) (hcomp n) i) atTop
      (𝓝 ((hmg i).toLp (fun x => deriv Ψ (u x) * gradOf hc hρ u i x))) := by
    intro i
    have hlim := tendsto_grad_comp_eLpNorm hc hρ hcpos hρpos hΨ hb hφ
      (tendsto_eLpNorm_gcls hc (h2 i)) h3
    unfold gcls
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    refine hlim.congr fun n => ?_
    rw [dpartial_comp hΨ (hφ n) i]
    rfl
  have hmem := mem_gradGraph_of_tendsto hc hρ (fun n x => Ψ (φ n x)) hcomp hv hh
  refine ⟨hΨu.toLp (fun x => Ψ (u x)), (mem_gradDomain_iff hc hρ _).2 ⟨_, hmem⟩,
    MemLp.coeFn_toLp _, fun i => ?_⟩
  rw [gradOf_spec hc hρ hcpos hρpos hmem]
  exact MemLp.coeFn_toLp _

theorem memLp_unitTruncation_wm {ρ : St d → ℝ} (u : Lp ℝ 2 (wm ρ)) :
    MemLp (fun x => DirichletForm.unitTruncation (u x)) 2 (wm ρ) := by
  exact LipschitzWith.comp_memLp DirichletForm.lipschitzWith_unitTruncation DirichletForm.unitTruncation_zero (Lp.memLp u)

theorem memLp_indicator_mul_wm {c ρ : St d → ℝ} (u : Lp ℝ 2 (wm ρ)) (g : Lp ℝ 2 (wm c)) :
    MemLp (fun x => Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) (u x) * g x) 2 (wm c) := by
  have h1 : Measurable (fun x => Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) (u x)) :=
    (measurable_const.indicator measurableSet_Ioo).comp (Lp.stronglyMeasurable u).measurable
  have hmeas : AEStronglyMeasurable
      (fun x => Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) (u x) * g x) (wm c) :=
    h1.aestronglyMeasurable.mul (Lp.stronglyMeasurable g).aestronglyMeasurable
  refine MemLp.of_le (Lp.memLp g) hmeas ?_
  filter_upwards with x
  by_cases hx : u x ∈ Ioo (0 : ℝ) 1
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

theorem tendsto_smoothClamp_comp_eLpNorm {ρ : St d → ℝ} (u : Lp ℝ 2 (wm ρ)) :
    Tendsto (fun k => eLpNorm (fun x => smoothClamp k (u x) -
      DirichletForm.unitTruncation (u x)) 2 (wm ρ)) atTop (𝓝 0) := by
  refine tendsto_eLpNorm_two_of_dominated (F := fun k x => smoothClamp k (u x))
    (f := fun x => DirichletForm.unitTruncation (u x)) (G := fun x => ‖u x‖)
    (Lp.memLp u).norm ?_ ?_ ?_
  · intro k
    exact ((smoothClamp_contDiff k).continuous.comp_stronglyMeasurable
      (Lp.stronglyMeasurable u)).aestronglyMeasurable
  · intro k
    filter_upwards with x
    exact (abs_smoothClamp_le k (u x)).trans_eq (Real.norm_eq_abs _).symm
  · filter_upwards with x
    exact smoothClamp_tendsto (u x)

theorem tendsto_smoothClampDeriv_mul_eLpNorm {c ρ : St d → ℝ} (u : Lp ℝ 2 (wm ρ))
    (g : Lp ℝ 2 (wm c)) (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) (hc : Continuous c)
    (hρ : Continuous ρ) :
    Tendsto (fun k => eLpNorm (fun x => smoothClampDeriv k (u x) * g x -
      Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) (u x) * g x) 2 (wm c)) atTop (𝓝 0) := by
  refine tendsto_eLpNorm_two_of_dominated
    (F := fun k x => smoothClampDeriv k (u x) * g x)
    (f := fun x => Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) (u x) * g x)
    (G := fun x => ‖g x‖) (Lp.memLp g).norm ?_ ?_ ?_
  · intro k
    exact (((smoothClampDeriv_contDiff k).continuous.comp_stronglyMeasurable
      (Lp.stronglyMeasurable u)).mul (Lp.stronglyMeasurable g)).aestronglyMeasurable
  · intro k
    filter_upwards with x
    have h := smoothClampDeriv_mem_Icc k (u x)
    rw [abs_mul, abs_of_nonneg h.1, ← Real.norm_eq_abs]
    calc smoothClampDeriv k (u x) * ‖g x‖ ≤ 1 * ‖g x‖ :=
          mul_le_mul_of_nonneg_right h.2 (norm_nonneg _)
      _ = ‖g x‖ := one_mul _
  · filter_upwards with x
    exact (smoothClampDeriv_tendsto (u x)).mul_const (g x)

/-- The unit truncation operates on the domain, with gradient `1_{0<u<1} ∇u`. -/
theorem unitTruncation_mem {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {u : Lp ℝ 2 (wm ρ)}
    (hu : u ∈ gradDomain hc hρ) :
    ∃ v : Lp ℝ 2 (wm ρ), v ∈ gradDomain hc hρ ∧
      (⇑v =ᵐ[wm ρ] fun x => DirichletForm.unitTruncation (u x)) ∧
      ∀ i, ⇑(gradOf hc hρ v i) =ᵐ[wm c] fun x =>
        Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) (u x) * gradOf hc hρ u i x := by
  have hb : ∀ k t, |deriv (smoothClamp k) t| ≤ 1 := fun k t => by
    rw [deriv_smoothClamp, abs_of_nonneg (smoothClampDeriv_mem_Icc k t).1]
    exact (smoothClampDeriv_mem_Icc k t).2
  choose v hvd hvae hvg using fun k =>
    compose_smooth_mem hc hρ hcpos hρpos (smoothClamp_contDiff k) (smoothClamp_zero k) (hb k) hu
  set vlim : Lp ℝ 2 (wm ρ) := (memLp_unitTruncation_wm u).toLp
    (fun x => DirichletForm.unitTruncation (u x)) with hvlim
  set hlim : Fin d → Lp ℝ 2 (wm c) := fun i => (memLp_indicator_mul_wm u (gradOf hc hρ u i)).toLp
    (fun x => Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) (u x) * gradOf hc hρ u i x)
    with hhlim
  have hv : Tendsto v atTop (𝓝 vlim) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine (tendsto_smoothClamp_comp_eLpNorm u).congr fun k => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hvae k, MemLp.coeFn_toLp (memLp_unitTruncation_wm u)] with x h1 h2
    simp only [Pi.sub_apply, h1]
    congr 1
    exact h2.symm
  have hh : ∀ i, Tendsto (fun k => gradOf hc hρ (v k) i) atTop (𝓝 (hlim i)) := by
    intro i
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine (tendsto_smoothClampDeriv_mul_eLpNorm u (gradOf hc hρ u i) hcpos hρpos hc hρ).congr
      fun k => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hvg k i, MemLp.coeFn_toLp (memLp_indicator_mul_wm u (gradOf hc hρ u i))]
      with x h1 h2
    simp only [Pi.sub_apply, h1, deriv_smoothClamp]
    congr 1
    exact h2.symm
  have hmem : (vlim, hlim) ∈ gradGraph hc hρ := by
    refine (isClosed_gradGraph hc hρ).mem_of_tendsto
      (f := fun k => (v k, fun i => gradOf hc hρ (v k) i)) (b := atTop) ?_ ?_
    · exact hv.prodMk_nhds (tendsto_pi_nhds.2 hh)
    · exact Eventually.of_forall fun k =>
        (mem_gradGraph_iff hc hρ hcpos hρpos _ _).2 ⟨hvd k, rfl⟩
  refine ⟨vlim, (mem_gradDomain_iff hc hρ _).2 ⟨_, hmem⟩, MemLp.coeFn_toLp _, fun i => ?_⟩
  rw [gradOf_spec hc hρ hcpos hρpos hmem]
  exact MemLp.coeFn_toLp _

/-- The energy of the truncation is at most the energy. -/
theorem gradForm_truncation_le {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {u v : Lp ℝ 2 (wm ρ)}
    (hu : u ∈ gradDomain hc hρ) (hv : v ∈ gradDomain hc hρ)
    (hgrad : ∀ i, ⇑(gradOf hc hρ v i) =ᵐ[wm c] fun x =>
        Set.indicator (Ioo (0 : ℝ) 1) (fun _ => (1 : ℝ)) (u x) * gradOf hc hρ u i x) :
    gradForm hc hρ v v ≤ gradForm hc hρ u u := by
  rw [gradForm_self hc hρ v, gradForm_self hc hρ u]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle : ‖gradOf hc hρ v i‖ ≤ ‖gradOf hc hρ u i‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hgrad i] with x hx
    rw [hx]
    by_cases hu' : u x ∈ Ioo (0 : ℝ) 1
    · simp [Set.indicator_of_mem hu']
    · simp [Set.indicator_of_notMem hu']
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- Test functions approximate a domain element in the energy norm. -/
theorem tendsto_energy_test_sequence {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {u : Lp ℝ 2 (wm ρ)}
    (hu : u ∈ gradDomain hc hρ) :
    ∃ (φ : ℕ → St d → ℝ) (hφ : ∀ n, φ n ∈ testFns d),
      Tendsto (fun n => (gradClosedForm hc hρ hcpos hρpos).energyNormSq
        (u - tcls hρ (φ n) (hφ n))) atTop (𝓝 0) := by
  obtain ⟨φs, hφs, h1, h2⟩ := exists_test_sequence hc hρ hcpos hρpos hu
  refine ⟨φs, hφs, ?_⟩
  have hform : ∀ k, (gradClosedForm hc hρ hcpos hρpos).energyNormSq
      (u - tcls hρ (φs k) (hφs k)) =
      ∑ i, ‖gradOf hc hρ u i - gcls hc (φs k) (hφs k) i‖ ^ 2 +
        ‖u - tcls hρ (φs k) (hφs k)‖ ^ 2 := fun k =>
    energyNormSq_sub_test hc hρ hcpos hρpos hu (hφs k)
  have hA : ∀ i, Tendsto (fun k => ‖gradOf hc hρ u i - gcls hc (φs k) (hφs k) i‖ ^ 2)
      atTop (𝓝 0) := by
    intro i
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 (h2 i)).pow 2)
    rw [zero_pow (by norm_num)] at this
    exact this.congr fun k => by rw [norm_sub_rev]
  have hB : Tendsto (fun k => ‖u - tcls hρ (φs k) (hφs k)‖ ^ 2) atTop (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 h1).pow 2)
    rw [zero_pow (by norm_num)] at this
    exact this.congr fun k => by rw [norm_sub_rev]
  have := (tendsto_finset_sum Finset.univ fun i _ => hA i).add hB
  simpa [hform] using this

/-- **The gradient form is a Dirichlet form.** -/
def gradDirichletForm {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) : _root_.DirichletForm (wm ρ) where
  toClosedForm := gradClosedForm hc hρ hcpos hρpos
  markov := fun u hu v hv => by
    obtain ⟨w, hwd, hwae, hwg⟩ := unitTruncation_mem hc hρ hcpos hρpos hu
    have hvw : v = w := by
      apply Lp.ext
      exact hv.trans hwae.symm
    subst hvw
    exact ⟨hwd, gradForm_truncation_le hc hρ hcpos hρpos hu hwd hwg⟩

/-- **Regularity**: the smooth compactly supported functions form a core. -/
theorem gradClosedForm_isRegular {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) :
    DirichletForm.IsRegular (gradClosedForm hc hρ hcpos hρpos) := by
  refine ⟨Set.univ, isOpen_univ, by simp, {w | ∃ φ, ∃ hφ : φ ∈ testFns d, w = tcls hρ φ hφ}, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro w ⟨φ, hφ, rfl⟩
    exact ⟨tcls_mem_gradDomain hc hρ hφ, φ, hφ.1.continuous, hφ.2, Set.subset_univ _,
      MemLp.coeFn_toLp _⟩
  · intro u hu ε hε
    obtain ⟨φ, hφ, hten⟩ := tendsto_energy_test_sequence hc hρ hcpos hρpos hu
    obtain ⟨n, hn⟩ := (hten.eventually (gt_mem_nhds hε)).exists
    exact ⟨tcls hρ (φ n) (hφ n), ⟨φ n, hφ n, rfl⟩, hn⟩
  · intro f hf hfc _ ε hε
    obtain ⟨ψ, hψ, hψc, hψs, hψf⟩ :=
      SubdiffusiveProcess.SmoothSources.exists_uniform_smooth_approximation f hf hfc Set.univ
        (Set.subset_univ _) ε hε
    exact ⟨tcls hρ ψ ⟨hψ, hψc⟩, ⟨ψ, ⟨hψ, hψc⟩, rfl⟩, ψ, hψ.continuous, hψc, hψs,
      MemLp.coeFn_toLp _, hψf⟩

end SubdiffusiveProcess.E7
