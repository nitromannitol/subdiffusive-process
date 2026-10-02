import SubdiffusiveProcess.Probability.Diffusion.HuntEarlyExit

/-!
# B4, B6, B7: `BrownianHuntContinuity d`

`ledger/reports/P-445-agent1.md` §4 and §7, the last three steps of the recommended route.  With
them, **target (iii) of the Brownian witness is proved**: `brownian_hunt_continuity`.

* `continuousOn_smoothing` (**B4**) — the free-Gaussian smoothing
  `F_delta(t,x,y) = ∫_U g_delta(x,w) q_{t-delta}(w,y) dw` is jointly continuous on
  `Ioi delta ×ˢ univ ×ˢ U`.  Fixed-measure dominated convergence: the measure does not move with
  `(t,x,y)`, the integrand is continuous in all three variables for every interior `w`, and near a
  point with `t₀ > delta` the horizon `t - delta` stays above `(t₀-delta)/2`, so the Gaussian
  constant `laplacianDensity_le_const_of_le` dominates uniformly.  This is the step the report
  designed the smoothing for: it establishes joint continuity *without* knowing any
  starting-point continuity of the killed density.
* `tendstoUniformlyOn_smoothing` (**B6**) — on `Icc a b ×ˢ Kx ×ˢ Ky` with `0 < a` and `Kx, Ky`
  compact in `U`, the smoothings converge uniformly as `delta ↓ 0`.  B5 bounds the error by
  `C_{t-delta} · P_x(τ_U ≤ delta)`; restricting to `delta < a/2` caps the first factor by
  `C_{a/2}`, and B3 makes the second uniformly small over `Kx`.
* `continuousOn_huntDensity_joint`, `brownian_hunt_continuity` (**B7**) — every point of
  `Ioi 0 ×ˢ U ×ˢ U` has a compact product neighbourhood `Icc (t₀/2) (t₀+1) ×ˢ closedBall ×ˢ
  closedBall` inside it (the ambient space is proper, so closed balls are compact); on it B4 and
  B6 give `TendstoUniformlyOn.continuousOn`, hence continuity of the killed density there, hence
  at the point.  B0 (`huntDensity_eq_sub`) then turns `q = g − H` into `H = g − q` and transfers
  the continuity to the exit correction, which is exactly `BrownianHuntContinuity d`.

`localDiffusionData_laplacianLaw_of_variational` records the consequence: the Brownian
`LocalDiffusionData (fun _ => 1) (fun _ => 1) (laplacianLaw d)` witness now rests on the
zero-boundary identification `BrownianVariationalIdentification d` **alone** — inputs (ii) and
(iii) are both discharged.

The route never assumes the form problem, never constructs a translated Brownian law, and uses no
regularity of `∂U`: only boundedness and openness of `U`.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The Gaussian constant is antitone in the time. -/
theorem laplacianDensity_le_const_of_le {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t) (x y : Vec d) :
    laplacianDensity t x y ≤ (Real.sqrt (4 * Real.pi * r))⁻¹ ^ d := by
  have ht : 0 < t := lt_of_lt_of_le hr hrt
  refine le_trans (laplacianDensity_le_const ht x y) ?_
  have hsr : 0 < Real.sqrt (4 * Real.pi * r) := Real.sqrt_pos.mpr (by positivity)
  have hmono : Real.sqrt (4 * Real.pi * r) ≤ Real.sqrt (4 * Real.pi * t) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [Real.pi_pos]
  have hinv : (Real.sqrt (4 * Real.pi * t))⁻¹ ≤ (Real.sqrt (4 * Real.pi * r))⁻¹ := by
    have h := one_div_le_one_div_of_le hsr hmono
    rwa [one_div, one_div] at h
  exact pow_le_pow_left₀ (by positivity) hinv d

/-- The free Gaussian is continuous in the starting point. -/
theorem continuous_laplacianDensity_start (t : ℝ) (y : Vec d) :
    Continuous (fun x : Vec d => laplacianDensity t x y) := by
  unfold laplacianDensity gaussianPDFReal
  fun_prop

/-- **B4 of the P-445 continuity route.**  The free-Gaussian smoothing of a killed row is jointly
continuous in the horizon, the starting point and the terminal point. -/
theorem continuousOn_smoothing {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {delta : ℝ} (hdelta : 0 < delta) :
    ContinuousOn (fun z : ℝ × Vec d × Vec d =>
        ∫ w in U, laplacianDensity delta z.2.1 w * huntDensity U (z.1 - delta) w z.2.2)
      (Ioi delta ×ˢ univ ×ˢ U) := by
  haveI := isFiniteMeasure_restrict_of_isBounded hUb
  rintro ⟨t₀, x₀, y₀⟩ ⟨ht₀, -, hy₀⟩
  refine ContinuousAt.continuousWithinAt ?_
  simp only [mem_Ioi] at ht₀
  set r : ℝ := (t₀ - delta) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hnbhd : {z : ℝ × Vec d × Vec d | delta + r < z.1} ∈ nhds ((t₀, x₀, y₀)) := by
    refine ((isOpen_lt continuous_const continuous_fst).mem_nhds ?_)
    show delta + r < t₀
    rw [hr]; linarith
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun _ : Vec d => (Real.sqrt (4 * Real.pi * delta))⁻¹ ^ d *
      (Real.sqrt (4 * Real.pi * r))⁻¹ ^ d)
    (Filter.Eventually.of_forall fun z => ?_) ?_ (integrable_const _) ?_
  · exact (Measurable.mul
      ((measurable_uncurry_laplacianDensity (d := d) delta).of_uncurry_left (x := z.2.1))
      ((measurable_uncurry_huntDensity U hU (z.1 - delta)).of_uncurry_right
        (y := z.2.2))).aestronglyMeasurable
  · filter_upwards [hnbhd] with z hz
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (laplacianDensity_nonneg delta z.2.1 w)
      (huntDensity_nonneg U (z.1 - delta) w z.2.2))]
    refine mul_le_mul (laplacianDensity_le_const hdelta _ _) ?_
      (huntDensity_nonneg U _ _ _) (by positivity)
    refine le_trans (Packet445Checks.huntDensity_le_laplacianDensity U (z.1 - delta) w z.2.2) ?_
    have hz1 : delta + r < z.1 := hz
    have hrle : r ≤ z.1 - delta := by linarith
    exact laplacianDensity_le_const_of_le hr0 hrle _ _
  · filter_upwards [ae_restrict_mem hU.measurableSet] with w hw
    have h1 : ContinuousAt (fun z : ℝ × Vec d × Vec d => laplacianDensity delta z.2.1 w)
        (t₀, x₀, y₀) :=
      ((continuous_laplacianDensity_start delta w).continuousAt).comp
        (continuous_snd.fst.continuousAt)
    have hopen : IsOpen (Ioi (0:ℝ) ×ˢ U) := isOpen_Ioi.prod hU
    have hAt : ContinuousAt (fun v : ℝ × Vec d => huntDensity U v.1 w v.2) (t₀ - delta, y₀) :=
      (Packet445Checks.continuousOn_huntDensity_time_end hU hw).continuousAt
        (hopen.mem_nhds ⟨by simp only [mem_Ioi]; linarith, hy₀⟩)
    have hpair : ContinuousAt
        (fun z : ℝ × Vec d × Vec d => ((z.1 - delta, z.2.2) : ℝ × Vec d)) (t₀, x₀, y₀) := by
      fun_prop
    have h2 : ContinuousAt
        (fun z : ℝ × Vec d × Vec d => huntDensity U (z.1 - delta) w z.2.2) (t₀, x₀, y₀) := by
      simpa [Function.comp_def] using
        ContinuousAt.comp (x := ((t₀, x₀, y₀) : ℝ × Vec d × Vec d)) hAt hpair
    exact h1.mul h2

/-- **B6 of the P-445 continuity route.**  On a compact product of a positive-time interval and
two compact interior sets, the smoothings converge uniformly to the killed density. -/
theorem tendstoUniformlyOn_smoothing {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    {Kx Ky : Set (Vec d)} (hKx : IsCompact Kx) (hKxU : Kx ⊆ U)
    (hKyU : Ky ⊆ U) :
    TendstoUniformlyOn
      (fun (delta : ℝ) (z : ℝ × Vec d × Vec d) =>
        ∫ w in U, laplacianDensity delta z.2.1 w * huntDensity U (z.1 - delta) w z.2.2)
      (fun z : ℝ × Vec d × Vec d => huntDensity U z.1 z.2.1 z.2.2)
      (𝓝[>] (0:ℝ)) (Icc a b ×ˢ Kx ×ˢ Ky) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  set C : ℝ := (Real.sqrt (4 * Real.pi * (a / 2)))⁻¹ ^ d with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  set e0 : ℝ := eps / (2 * (C + 1)) with he0
  have he0pos : 0 < e0 := by rw [he0]; positivity
  obtain ⟨a', ha', hexit⟩ :=
    exists_uniform_early_exit hU Kx hKx hKxU (eps := ENNReal.ofReal e0)
      (ENNReal.ofReal_pos.mpr he0pos)
  have hmem : Ioo (0:ℝ) (min (a / 2) a') ∈ 𝓝[>] (0:ℝ) :=
    Ioo_mem_nhdsGT (lt_min (by linarith) ha')
  filter_upwards [hmem] with delta hdelta
  obtain ⟨hd0, hdlt⟩ := hdelta
  intro z hz
  obtain ⟨hz1, hz2, hz3⟩ := hz
  have hda : delta < a / 2 := lt_of_lt_of_le hdlt (min_le_left _ _)
  have hda' : delta ≤ a' := le_of_lt (lt_of_lt_of_le hdlt (min_le_right _ _))
  have hz1a : a ≤ z.1 := hz1.1
  have hdz : delta < z.1 := by linarith
  have hbound := abs_smoothing_error_le hU hUb hd0 hdz (hKxU hz2) (hKyU hz3)
  have hconst : (Real.sqrt (4 * Real.pi * (z.1 - delta)))⁻¹ ^ d ≤ C := by
    rw [hC]
    have hsr : 0 < Real.sqrt (4 * Real.pi * (a / 2)) := Real.sqrt_pos.mpr (by positivity)
    have hmono : Real.sqrt (4 * Real.pi * (a / 2)) ≤ Real.sqrt (4 * Real.pi * (z.1 - delta)) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith [Real.pi_pos]
    have hinv : (Real.sqrt (4 * Real.pi * (z.1 - delta)))⁻¹
        ≤ (Real.sqrt (4 * Real.pi * (a / 2)))⁻¹ := by
      have h := one_div_le_one_div_of_le hsr hmono
      rwa [one_div, one_div] at h
    exact pow_le_pow_left₀ (by positivity) hinv d
  have hprob : (laplacianContinuousLaw d z.2.1
      {w | ContinuousPath.exitTime U w ≤ ENNReal.ofReal delta}).toReal ≤ e0 := by
    have hle := hexit delta hd0 hda' z.2.1 hz2
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal he0pos.le] at this
  have hprobnn : 0 ≤ (laplacianContinuousLaw d z.2.1
      {w | ContinuousPath.exitTime U w ≤ ENNReal.ofReal delta}).toReal := ENNReal.toReal_nonneg
  rw [Real.dist_eq, abs_sub_comm]
  have hstep : |(∫ w in U, laplacianDensity delta z.2.1 w * huntDensity U (z.1 - delta) w z.2.2) -
      huntDensity U z.1 z.2.1 z.2.2| ≤ C * e0 :=
    le_trans hbound (mul_le_mul hconst hprob hprobnn hC0)
  refine lt_of_le_of_lt hstep ?_
  have hden : (0:ℝ) < 2 * (C + 1) := by positivity
  have hrw : C * e0 = (C * eps) / (2 * (C + 1)) := by rw [he0]; ring
  rw [hrw, div_lt_iff₀ hden]
  nlinarith

/-- Closed balls in the ambient space are compact. -/
theorem isCompact_closedBall_vec (x : Vec d) (r : ℝ) :
    IsCompact (Metric.closedBall x r) := isCompact_closedBall x r

/-- **B7 of the P-445 continuity route: `BrownianHuntContinuity d`.**  The exit correction is
jointly continuous on `Ioi 0 ×ˢ U ×ˢ U`. -/
theorem continuousOn_huntDensity_joint {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    ContinuousOn (fun z : ℝ × Vec d × Vec d => huntDensity U z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ U ×ˢ U) := by
  rintro ⟨t₀, x₀, y₀⟩ ⟨ht₀, hx₀, hy₀⟩
  simp only [mem_Ioi] at ht₀
  obtain ⟨rx, hrx, hrxU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  obtain ⟨ry, hry, hryU⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  set a : ℝ := t₀ / 2 with ha
  set b : ℝ := t₀ + 1 with hb
  set Kx : Set (Vec d) := Metric.closedBall x₀ (rx / 2) with hKx
  set Ky : Set (Vec d) := Metric.closedBall y₀ (ry / 2) with hKy
  have ha0 : 0 < a := by rw [ha]; linarith
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hKxU : Kx ⊆ U := fun p hp => hrxU (Metric.mem_ball.mpr
    (lt_of_le_of_lt (Metric.mem_closedBall.mp hp) (by linarith)))
  have hKyU : Ky ⊆ U := fun p hp => hryU (Metric.mem_ball.mpr
    (lt_of_le_of_lt (Metric.mem_closedBall.mp hp) (by linarith)))
  set S : Set (ℝ × Vec d × Vec d) := Icc a b ×ˢ Kx ×ˢ Ky with hS
  have hSnbhd : S ∈ nhds ((t₀, x₀, y₀) : ℝ × Vec d × Vec d) := by
    have hopen : IsOpen (Ioo a b ×ˢ Metric.ball x₀ (rx / 2) ×ˢ Metric.ball y₀ (ry / 2)) :=
      isOpen_Ioo.prod (Metric.isOpen_ball.prod Metric.isOpen_ball)
    refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
    · exact ⟨⟨by rw [ha]; linarith, by rw [hb]; linarith⟩,
        Metric.mem_ball_self (by linarith), Metric.mem_ball_self (by linarith)⟩
    · rintro ⟨u, p, q⟩ ⟨hu, hp, hq⟩
      exact ⟨⟨hu.1.le, hu.2.le⟩, Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp).le,
        Metric.mem_closedBall.mpr (Metric.mem_ball.mp hq).le⟩
  have hev : ∀ᶠ delta in 𝓝[>] (0:ℝ), ContinuousOn
      (fun z : ℝ × Vec d × Vec d =>
        ∫ w in U, laplacianDensity delta z.2.1 w * huntDensity U (z.1 - delta) w z.2.2) S := by
    filter_upwards [Ioo_mem_nhdsGT ha0] with delta hdelta
    refine ContinuousOn.mono (continuousOn_smoothing hU hUb hdelta.1) ?_
    rintro ⟨u, p, q⟩ ⟨hu, hp, hq⟩
    exact ⟨lt_of_lt_of_le hdelta.2 hu.1, trivial, hKyU hq⟩
  have hcontS : ContinuousOn (fun z : ℝ × Vec d × Vec d => huntDensity U z.1 z.2.1 z.2.2) S :=
    TendstoUniformlyOn.continuousOn
      (tendstoUniformlyOn_smoothing hU hUb ha0 hab (isCompact_closedBall_vec x₀ (rx / 2))
        hKxU hKyU) hev.frequently
  exact (hcontS.continuousAt hSnbhd).continuousWithinAt

/-- **`BrownianHuntContinuity d`.**  The exit correction is jointly continuous on the interior. -/
theorem brownian_hunt_continuity (d : ℕ) : BrownianHuntContinuity d := by
  intro U hU hUb
  have hq := continuousOn_huntDensity_joint hU hUb
  have hg : ContinuousOn (fun z : ℝ × Vec d × Vec d => laplacianDensity z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ U ×ˢ U) :=
    continuousOn_laplacianDensity.mono (fun z hz => ⟨hz.1, trivial, trivial⟩)
  have heq : EqOn (fun z : ℝ × Vec d × Vec d => huntCorrection U z.1 z.2.1 z.2.2)
      (fun z : ℝ × Vec d × Vec d =>
        laplacianDensity z.1 z.2.1 z.2.2 - huntDensity U z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ U ×ˢ U) := by
    rintro ⟨t, x, y⟩ ⟨ht, hx, hy⟩
    have := huntDensity_eq_sub hU hUb (by simpa using ht) hx hy
    simp only
    linarith
  exact (hg.sub hq).congr heq



theorem localDiffusionData_laplacianLaw_of_variational (d : ℕ)
    (hpart : BrownianVariationalIdentification d) :
    LocalDiffusionData (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (laplacianLaw d) :=
  localDiffusionData_laplacianLaw_of_two_inputs d hpart (brownian_hunt_continuity d)

/-- The existence form, on the one remaining input. -/
theorem exists_localDiffusionData_const_of_variational (d : ℕ)
    (hpart : BrownianVariationalIdentification d) :
    ∃ law : Kernel (Vec d) (Path d),
      LocalDiffusionData (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) law :=
  ⟨laplacianLaw d, localDiffusionData_laplacianLaw_of_variational d hpart⟩

end SubdiffusiveProcess.Probability.Diffusion
