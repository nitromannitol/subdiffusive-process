import SubdiffusiveProcess.Probability.Diffusion.GaussianEnvelope
import SubdiffusiveProcess.Probability.Diffusion.HuntCorrection
import SubdiffusiveProcess.Probability.Diffusion.Brownian
import SubdiffusiveProcess.Probability.Diffusion.HuntIdentity




set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion
variable {d : ℕ}

/-- **The master pathwise envelope.**  On a path whose exit point lies outside `U`, the exit
integrand is dominated by the separated Gaussian envelope at the remaining time, with the
squared separation of an interior ball from the complement.  All three regimes are covered: an
infinite exit time, an exit after the horizon, and an exit before it. -/
theorem abs_huntIntegrand_le_envelope {U : Set (Vec d)} {y₀ : Vec d} {δ : ℝ}
    (hδ : 0 < δ) (hball : Metric.ball y₀ (2 * δ) ⊆ U)
    {w : ContinuousPath (Vec d)}
    (hw : ContinuousPath.exitTime U w ≠ ⊤ →
      w ((ContinuousPath.exitTime U w).toNNReal) ∉ U)
    (t : ℝ) {y : Vec d} (hy : y ∈ Metric.ball y₀ δ) :
    |huntIntegrand U t y w| ≤
      boundaryGaussianEnvelope d (δ ^ 2) (t - (ContinuousPath.exitTime U w).toReal) := by
  classical
  set tau : ℝ≥0∞ := ContinuousPath.exitTime U w with htau
  by_cases hlt : tau < ENNReal.ofReal t
  · -- the exit is strictly before the horizon: in particular it is finite
    have hfin : tau ≠ ⊤ := ne_top_of_lt hlt
    have htpos : 0 < t := by
      by_contra hneg
      push_neg at hneg
      rw [ENNReal.ofReal_of_nonpos hneg] at hlt
      exact absurd hlt (by simp)
    have hpos : 0 < t - tau.toReal := by
      have h1 : tau.toReal < t := by
        have h2 := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hlt
        rwa [ENNReal.toReal_ofReal htpos.le] at h2
      linarith
    have hval : huntIntegrand U t y w =
        laplacianDensity (t - tau.toReal) (w tau.toNNReal) y := by
      unfold huntIntegrand
      rw [Set.indicator_of_mem (by exact hlt)]
    rw [hval, abs_of_nonneg (laplacianDensity_nonneg _ _ _),
      boundaryGaussianEnvelope, if_pos hpos]
    exact laplacianDensity_le_of_sq_separation hpos _ _
      (sq_separation_of_ball_subset hδ hball hy (hw hfin))
  · have hval : huntIntegrand U t y w = 0 := by
      unfold huntIntegrand
      rw [Set.indicator_of_notMem (by exact hlt)]
    rw [hval, abs_zero]
    exact boundaryGaussianEnvelope_nonneg _ _ _

/-- The exit integrand is continuous in the horizon and the terminal point, **for every path**
whose exit point lies outside `U` -- including at the critical horizon `t = tau(w)`, where the
Gaussian envelope forces the value to zero rather than jump. -/
theorem continuousAt_huntIntegrand {U : Set (Vec d)} {y₀ : Vec d} {δ : ℝ}
    (hδ : 0 < δ) (hball : Metric.ball y₀ (2 * δ) ⊆ U)
    {w : ContinuousPath (Vec d)}
    (hw : ContinuousPath.exitTime U w ≠ ⊤ →
      w ((ContinuousPath.exitTime U w).toNNReal) ∉ U)
    {t₀ : ℝ} (ht₀ : 0 < t₀) {y : Vec d} (hy : y ∈ Metric.ball y₀ δ) :
    ContinuousAt (fun z : ℝ × Vec d => huntIntegrand U z.1 z.2 w) (t₀, y) := by
  classical
  set tau : ℝ≥0∞ := ContinuousPath.exitTime U w with htau
  by_cases hfin : tau = ⊤
  · -- the path never leaves `U`: the integrand vanishes identically
    have hzero : (fun z : ℝ × Vec d => huntIntegrand U z.1 z.2 w) = fun _ => (0 : ℝ) := by
      funext z
      unfold huntIntegrand
      refine Set.indicator_of_notMem ?_ _
      show ¬ (tau < ENNReal.ofReal z.1)
      rw [hfin]
      exact fun hcon => absurd hcon (by simp)
    rw [hzero]
    exact continuousAt_const
  · set t1 : ℝ := tau.toReal with ht1
    have ht1nn : 0 ≤ t1 := ENNReal.toReal_nonneg
    have htaueq : tau = ENNReal.ofReal t1 := (ENNReal.ofReal_toReal hfin).symm
    have hiff : ∀ r : ℝ, 0 ≤ r → (tau < ENNReal.ofReal r ↔ t1 < r) := by
      intro r hr
      rw [htaueq, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht1nn]
    rcases lt_trichotomy t1 t₀ with hlt | heq | hgt
    · -- strict exit before the horizon: the free Gaussian is continuous there
      have hopen : {z : ℝ × Vec d | t1 < z.1} ∈ 𝓝 ((t₀, y) : ℝ × Vec d) :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds hlt
      have hcong : (fun z : ℝ × Vec d => huntIntegrand U z.1 z.2 w)
          =ᶠ[𝓝 ((t₀, y) : ℝ × Vec d)]
          fun z : ℝ × Vec d => laplacianDensity (z.1 - t1) (w tau.toNNReal) z.2 := by
        filter_upwards [hopen] with z hz
        have hzlt : t1 < z.1 := hz
        have hmem : w ∈ {v : ContinuousPath (Vec d) |
            ContinuousPath.exitTime U v < ENNReal.ofReal z.1} :=
          (hiff z.1 (le_trans ht1nn hzlt.le)).mpr hzlt
        show Set.indicator {v : ContinuousPath (Vec d) |
            ContinuousPath.exitTime U v < ENNReal.ofReal z.1}
          (fun v => laplacianDensity (z.1 - (ContinuousPath.exitTime U v).toReal)
            (v (ContinuousPath.exitTime U v).toNNReal) z.2) w = _
        rw [Set.indicator_of_mem hmem]
      have hbase : ContinuousAt
          (fun z : ℝ × Vec d => laplacianDensity (z.1 - t1) (w tau.toNNReal) z.2) (t₀, y) := by
        have hmem : ((t₀ - t1, (w tau.toNNReal, y)) : ℝ × Vec d × Vec d) ∈
            Ioi (0:ℝ) ×ˢ (univ : Set (Vec d)) ×ˢ (univ : Set (Vec d)) :=
          ⟨(show (0:ℝ) < t₀ - t1 from sub_pos.mpr hlt), mem_univ _, mem_univ _⟩
        have hcontAt := (continuousOn_laplacianDensity (d := d)).continuousAt
          (((isOpen_Ioi.prod (isOpen_univ.prod isOpen_univ)).mem_nhds hmem))
        have hg : ContinuousAt
            (fun z : ℝ × Vec d => ((z.1 - t1, (w tau.toNNReal, z.2)) : ℝ × Vec d × Vec d))
            (t₀, y) :=
          (((continuous_fst.sub continuous_const).prodMk
            (continuous_const.prodMk continuous_snd)).continuousAt)
        have hcomp : ContinuousAt
            ((fun z : ℝ × Vec d × Vec d => laplacianDensity z.1 z.2.1 z.2.2) ∘
              (fun z : ℝ × Vec d => ((z.1 - t1, (w tau.toNNReal, z.2)) : ℝ × Vec d × Vec d)))
            (t₀, y) := ContinuousAt.comp hcontAt hg
        exact hcomp
      exact hbase.congr hcong.symm
    · -- the critical horizon: the envelope squeezes the value to zero
      have hval : huntIntegrand U t₀ y w = 0 := by
        unfold huntIntegrand
        refine Set.indicator_of_notMem ?_ _
        show ¬ (tau < ENNReal.ofReal t₀)
        rw [hiff t₀ ht₀.le]
        exact not_lt.mpr heq.ge
      rw [ContinuousAt, hval]
      have hball' : (fun z : ℝ × Vec d => z.2) ⁻¹' Metric.ball y₀ δ ∈
          𝓝 ((t₀, y) : ℝ × Vec d) :=
        continuous_snd.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hy)
      refine squeeze_zero_norm'
        (a := fun z : ℝ × Vec d => boundaryGaussianEnvelope d (δ ^ 2) (z.1 - t1)) ?_ ?_
      · filter_upwards [hball'] with z hz
        exact abs_huntIntegrand_le_envelope hδ hball hw z.1 hz
      · have hcont : Continuous
            (fun z : ℝ × Vec d => boundaryGaussianEnvelope d (δ ^ 2) (z.1 - t1)) :=
          (continuous_boundaryGaussianEnvelope (d := d) (by positivity)).comp
            (continuous_fst.sub continuous_const)
        have := hcont.continuousAt (x := ((t₀, y) : ℝ × Vec d))
        rw [ContinuousAt] at this
        simpa [heq] using this
    · -- the exit is after the horizon: the integrand vanishes near it
      have hopen : {z : ℝ × Vec d | z.1 < t1} ∈ 𝓝 ((t₀, y) : ℝ × Vec d) :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hgt
      have hval : huntIntegrand U t₀ y w = 0 := by
        unfold huntIntegrand
        refine Set.indicator_of_notMem ?_ _
        show ¬ (tau < ENNReal.ofReal t₀)
        rw [hiff t₀ ht₀.le]
        exact not_lt.mpr hgt.le
      rw [ContinuousAt, hval]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hopen] with z hz
      unfold huntIntegrand
      symm
      refine Set.indicator_of_notMem ?_ _
      show ¬ (tau < ENNReal.ofReal z.1)
      rcases le_or_gt (0:ℝ) z.1 with hz0 | hz0
      · rw [hiff z.1 hz0]
        exact not_lt.mpr hz.le
      · rw [ENNReal.ofReal_of_nonpos hz0.le]
        exact fun hcon => absurd hcon (by simp)

/-- **Target (iii) at a fixed interior starting point.**  The exit correction is jointly
continuous in the horizon and the terminal point on `Ioi 0 ×ˢ U`, for every start `x ∈ U`.
Dominated convergence applies: the law does not move, the integrand is continuous in
`(t, y)` for almost every path by `continuousAt_huntIntegrand`, and the separated Gaussian
envelope is a uniform constant bound on any finite horizon. -/
theorem continuousAt_huntCorrection_start {U : Set (Vec d)} (hU : IsOpen U)
    {x : Vec d} (hx : x ∈ U) {t₀ : ℝ} (ht₀ : 0 < t₀) {y₀ : Vec d} (hy₀ : y₀ ∈ U) :
    ContinuousAt (fun z : ℝ × Vec d => huntCorrection U z.1 x z.2) (t₀, y₀) := by
  classical
  letI : IsMarkovKernel (laplacianContinuousLaw d) := by
    unfold laplacianContinuousLaw; infer_instance
  obtain ⟨δ0, hδ0, hball0⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  set δ : ℝ := δ0 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hball : Metric.ball y₀ (2 * δ) ⊆ U := by
    have : 2 * δ = δ0 := by rw [hδdef]; ring
    rw [this]; exact hball0
  have hy₀δ : y₀ ∈ Metric.ball y₀ δ := Metric.mem_ball_self hδ
  -- almost every path starts at `x` and therefore exits outside `U`
  have hae : ∀ᵐ w ∂(laplacianContinuousLaw d x),
      ContinuousPath.exitTime U w ≠ ⊤ →
        w ((ContinuousPath.exitTime U w).toNNReal) ∉ U := by
    filter_upwards [SubMarkovKernelSemigroup.IsConservative.ae_eval_zero_eq
      isConservative_laplacianSemigroup kolmogorovRegular_laplacianSemigroup x] with w hw hfin
    have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU w (hw ▸ hx) hfin
    exact fun hmem => ((hU.frontier_eq ▸ hfront).2) hmem
  obtain ⟨C, hC0, hCbound⟩ :=
    exists_bound_boundaryGaussianEnvelope (d := d) (a := δ ^ 2) (by positivity) (t₀ + 1)
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => C) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun z => ?_
    refine Measurable.aestronglyMeasurable ?_
    exact (measurable_huntIntegrand U hU).comp (measurable_const.prodMk measurable_id)
  · have hnbhd : {z : ℝ × Vec d | z.1 < t₀ + 1 ∧ z.2 ∈ Metric.ball y₀ δ} ∈
        𝓝 ((t₀, y₀) : ℝ × Vec d) := by
      refine ((isOpen_lt continuous_fst continuous_const).inter
        (continuous_snd.isOpen_preimage _ Metric.isOpen_ball)).mem_nhds ?_
      exact ⟨show t₀ < t₀ + 1 by linarith, hy₀δ⟩
    filter_upwards [hnbhd] with z hz
    filter_upwards [hae] with w hw
    have hbase := abs_huntIntegrand_le_envelope hδ hball hw z.1 hz.2
    refine le_trans hbase ?_
    rcases le_or_gt 0 (z.1 - (ContinuousPath.exitTime U w).toReal) with hr | hr
    · refine hCbound _ ⟨hr, ?_⟩
      have := ENNReal.toReal_nonneg (a := ContinuousPath.exitTime U w)
      linarith [hz.1]
    · rw [boundaryGaussianEnvelope, if_neg (not_lt.mpr hr.le)]
      exact hC0
  · exact integrable_const C
  · filter_upwards [hae] with w hw
    exact continuousAt_huntIntegrand hδ hball hw ht₀ hy₀δ

/-- The `ContinuousOn` form on the open product. -/
theorem continuousOn_huntCorrection_start {U : Set (Vec d)} (hU : IsOpen U)
    {x : Vec d} (hx : x ∈ U) :
    ContinuousOn (fun z : ℝ × Vec d => huntCorrection U z.1 x z.2) (Ioi 0 ×ˢ U) := by
  intro z hz
  exact (continuousAt_huntCorrection_start hU hx hz.1 hz.2).continuousWithinAt

end SubdiffusiveProcess.Probability.Diffusion
