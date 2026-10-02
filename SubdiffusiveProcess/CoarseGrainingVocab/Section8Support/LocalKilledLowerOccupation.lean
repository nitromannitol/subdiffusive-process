import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerPotential
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernel




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ}

/-! ### Monotonicity of the exit time in the domain -/

/-- A path leaves a smaller set no later: `τ_V ≤ τ_W` for `V ⊆ W`.  The manuscript's Poisson
correction is solved on an inner set `B ⊆ U`, so its mean exit time is controlled by the one
assumed on `U`. -/
theorem exitTime_mono {V W : Set (Vec d)} (hVW : V ⊆ W) (w : Path d) :
    LifetimePath.exitTime V w ≤ LifetimePath.exitTime W w := by
  refine sInf_le_sInf ?_
  rintro s ⟨t, rfl, hnot⟩
  exact ⟨t, rfl, fun hmem => hnot (Set.image_mono hVW hmem)⟩

/-- The mean exit time is monotone in the domain. -/
theorem meanExit_mono (law : Kernel (Vec d) (Path d)) {V W : Set (Vec d)} (hVW : V ⊆ W)
    (z : Vec d) : meanExit law V z ≤ meanExit law W z :=
  lintegral_mono fun w => exitTime_mono hVW w

/-! ### The Laplace integrand -/

/-- The time-`t` survival integral `t ↦ E_y[q(X_t); t < τ_W]` is measurable. -/
theorem measurable_survivalIntegral (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {W : Set (Vec d)} (hW : IsOpen W) {q : Vec d → ℝ} (hq : Measurable q) (z : Vec d) :
    Measurable (fun t : ℝ =>
      ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w},
        q (position (Real.toNNReal t) w) ∂law z) := by
  classical
  have hjoint : Measurable (fun r : ℝ × Path d =>
      if ENNReal.ofReal r.1 < LifetimePath.exitTime W r.2 then
        q (position (Real.toNNReal r.1) r.2) else 0) :=
    Measurable.ite (survival_measurable W hW) (hq.comp joint_position) measurable_const
  have hrw : (fun t : ℝ =>
      ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w},
        q (position (Real.toNNReal t) w) ∂law z)
      = fun t : ℝ => ∫ w, (if ENNReal.ofReal t < LifetimePath.exitTime W w then
          q (position (Real.toNNReal t) w) else 0) ∂law z := by
    funext t
    rw [← integral_indicator
      (measurableSet_lt measurable_const (localTorsion_exitTime_measurable W hW))]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hrw]
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- The survival probability of `W` is integrable on the half line as soon as the mean exit
time is finite; its integral is the mean exit time. -/
theorem integrableOn_survival (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {W : Set (Vec d)} (hW : IsOpen W) {E : ℝ} {z : Vec d}
    (hz : meanExit law W z ≤ ENNReal.ofReal E) :
    IntegrableOn (fun t : ℝ =>
      (law z {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal) (Ioi 0) := by
  have hlint : (∫⁻ t in Ioi (0:ℝ),
      law z {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}) = meanExit law W z :=
    (meanExit_eq_lintegral_survival law hW z).symm
  have hne : (∫⁻ t in Ioi (0:ℝ),
      law z {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}) ≠ ∞ := by
    rw [hlint]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hz
  exact integrable_toReal_of_lintegral_ne_top
    ((survival_antitone law W z).measurable.aemeasurable) hne

/-- The integral of the survival probability is the mean exit time, hence bounded by any
bound on it. -/
theorem integral_survival_le (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {W : Set (Vec d)} (hW : IsOpen W) {E : ℝ} (hE : 0 ≤ E) {z : Vec d}
    (hz : meanExit law W z ≤ ENNReal.ofReal E) :
    (∫ t in Ioi (0:ℝ),
      (law z {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal) ≤ E := by
  have hEq : (∫ t in Ioi (0:ℝ),
        (law z {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal)
      = (∫⁻ t in Ioi (0:ℝ),
        law z {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal :=
    integral_toReal ((survival_antitone law W z).measurable.aemeasurable)
      (Eventually.of_forall fun t => lt_of_le_of_ne le_top (measure_ne_top _ _))
  rw [hEq, ← meanExit_eq_lintegral_survival law hW z]
  calc (meanExit law W z).toReal ≤ (ENNReal.ofReal E).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hz
    _ = E := ENNReal.toReal_ofReal hE

/-- The time-`t` survival integral of a function bounded by `K` on `W` is bounded by `K`
times the survival probability. -/
theorem abs_survivalIntegral_le (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {W : Set (Vec d)} {q : Vec d → ℝ} {K : ℝ} (hqb : ∀ x ∈ W, |q x| ≤ K) (z : Vec d)
    (t : ℝ) :
    |∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w},
        q (position (Real.toNNReal t) w) ∂law z|
      ≤ K * (law z {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal := by
  have hmem : ∀ w ∈ {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w},
      |q (position (Real.toNNReal t) w)| ≤ K := by
    intro w hw
    exact hqb _ (localTorsion_position_mem W w (Real.toNNReal t) hw)
  have h := norm_setIntegral_le_of_norm_le_const (μ := law z)
    (s := {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w})
    (f := fun w => q (position (Real.toNNReal t) w)) (measure_lt_top _ _) hmem
  simpa only [Real.norm_eq_abs, Measure.real] using h

/-- `s · R_s^W q` is the Laplace transform of the survival integrals. -/
theorem mul_killedResolvent_eq (law : Kernel (Vec d) (Path d)) (W : Set (Vec d))
    (q : Vec d → ℝ) (z : Vec d) {s : ℝ} (hs : 0 < s) :
    s * killedResolvent law W s q z
      = ∫ t in Ioi (0:ℝ), Real.exp (-t / s) *
          ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w},
            q (position (Real.toNNReal t) w) ∂law z := by
  rw [killedResolvent, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

/-- **The maximum principle for the killed resolvent**: `|s R_s^W q| ≤ K · sup_W e_W` for
`|q| ≤ K` on `W`.  This is the resolvent form of `abs_occupationPotential_le`. -/
theorem abs_mul_killedResolvent_le (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {W : Set (Vec d)} (hW : IsOpen W) {q : Vec d → ℝ} (hq : Measurable q) {K E : ℝ}
    (hK : 0 ≤ K) (hE : 0 ≤ E) (hqb : ∀ x ∈ W, |q x| ≤ K) {z : Vec d}
    (hz : meanExit law W z ≤ ENNReal.ofReal E) {s : ℝ} (hs : 0 < s) :
    |s * killedResolvent law W s q z| ≤ K * E := by
  rw [mul_killedResolvent_eq law W q z hs]
  set g : ℝ → ℝ := fun t =>
    ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w},
      q (position (Real.toNNReal t) w) ∂law z with hg
  set P : ℝ → ℝ := fun t =>
    (law z {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal with hP
  have hgmeas : Measurable g := measurable_survivalIntegral law hW hq z
  have hPint : IntegrableOn P (Ioi 0) := integrableOn_survival law hW hz
  have hgb : ∀ t, |g t| ≤ K * P t := fun t => abs_survivalIntegral_le law hqb z t
  have hdom : ∀ t ∈ Ioi (0:ℝ), ‖Real.exp (-t / s) * g t‖ ≤ K * P t := by
    intro t ht
    have hexp : Real.exp (-t / s) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      rw [neg_div]
      have : (0:ℝ) ≤ t / s := div_nonneg (le_of_lt ht) hs.le
      linarith
    calc ‖Real.exp (-t / s) * g t‖ = Real.exp (-t / s) * |g t| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * (K * P t) :=
          mul_le_mul hexp (hgb t) (abs_nonneg _) zero_le_one
      _ = K * P t := one_mul _
  have hmeas : AEStronglyMeasurable (fun t => Real.exp (-t / s) * g t)
      (volume.restrict (Ioi 0)) :=
    (((Real.measurable_exp.comp (measurable_id.neg.div_const s))).mul
      hgmeas).aestronglyMeasurable
  have hint : IntegrableOn (fun t => Real.exp (-t / s) * g t) (Ioi 0) := by
    refine Integrable.mono (hPint.const_mul K) hmeas ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have h := hdom t ht
    have hnn : 0 ≤ K * P t := le_trans (norm_nonneg _) h
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using h
  calc |∫ t in Ioi (0:ℝ), Real.exp (-t / s) * g t|
      ≤ ∫ t in Ioi (0:ℝ), ‖Real.exp (-t / s) * g t‖ := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi (0:ℝ), K * P t :=
        setIntegral_mono_on hint.norm (hPint.const_mul K) measurableSet_Ioi hdom
    _ = K * ∫ t in Ioi (0:ℝ), P t := integral_const_mul _ _
    _ ≤ K * E := mul_le_mul_of_nonneg_left (integral_survival_le law hW hE hz) hK

/-- **The occupation potential is the zero-mass limit of the killed resolvent**:
`v(y) = lim_{s → ∞} s · R_s^W q (y)`, the identity recorded in the docstring of
`occupationPotential`.  This is the analytic entry point of the Poisson representation:
the `LocalDiffusion` resolvent clause controls `s · R_s^W q` for every finite `s`. -/
theorem tendsto_mul_killedResolvent_occupationPotential
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law] {W : Set (Vec d)} (hW : IsOpen W)
    {q : Vec d → ℝ} (hq : Measurable q) {K E : ℝ} (hqb : ∀ x ∈ W, |q x| ≤ K) {z : Vec d}
    (hz : meanExit law W z ≤ ENNReal.ofReal E) :
    Tendsto (fun s : ℝ => s * killedResolvent law W s q z) atTop
      (𝓝 (occupationPotential law W q z)) := by
  rw [occupationPotential]
  set g : ℝ → ℝ := fun t =>
    ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w},
      q (position (Real.toNNReal t) w) ∂law z with hg
  set P : ℝ → ℝ := fun t =>
    (law z {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}).toReal with hP
  have hgmeas : Measurable g := measurable_survivalIntegral law hW hq z
  have hPint : IntegrableOn P (Ioi 0) := integrableOn_survival law hW hz
  have hgb : ∀ t, |g t| ≤ K * P t := fun t => abs_survivalIntegral_le law hqb z t
  have hmain : Tendsto (fun s : ℝ => ∫ t in Ioi (0:ℝ), Real.exp (-t / s) * g t) atTop
      (𝓝 (∫ t in Ioi (0:ℝ), g t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => K * P t) ?_ ?_
      (hPint.const_mul K) ?_
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with s _
      exact (((Real.measurable_exp.comp (measurable_id.neg.div_const s))).mul
        hgmeas).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have hexp : Real.exp (-t / s) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        rw [neg_div]
        have : (0:ℝ) ≤ t / s := div_nonneg (le_of_lt ht) hs.le
        linarith
      calc ‖Real.exp (-t / s) * g t‖ = Real.exp (-t / s) * |g t| := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ 1 * (K * P t) := mul_le_mul hexp (hgb t) (abs_nonneg _) zero_le_one
        _ = K * P t := one_mul _
    · filter_upwards [] with t
      have h1 : Tendsto (fun s : ℝ => -t / s) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h2 : Tendsto (fun s : ℝ => Real.exp (-t / s)) atTop (𝓝 1) := by
        simpa using (Real.continuous_exp.tendsto 0).comp h1
      simpa using h2.mul_const (g t)
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
  exact (mul_killedResolvent_eq law W q z hs).symm

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
