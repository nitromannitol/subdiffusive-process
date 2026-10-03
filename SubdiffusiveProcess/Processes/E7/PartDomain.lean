module

public import SubdiffusiveProcess.Processes.E7.CutoffApproximation
public import SubdiffusiveProcess.Processes.E7.Leaves
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput

@[expose] public section

/-!
# The part form: boundary approximation and the weak equation of its resolvent

The analytic half of the killed-generator identification: the resolvent `G^U_α f` of the part form
of the gradient form on a bounded open set `U` is (the restriction of) a domain element, is
approximated in `H¹` by smooth functions with compact support in `U`, and satisfies the weak equation
`α ∫_U ρ u ψ + ∫_U c ∇u · ∇ψ = ∫_U ρ f ψ` for smooth test functions supported in `U`.
-/
open MeasureTheory Filter Set Topology Homogenization
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- The inner product of `L²(w dx | U)` as a Lebesgue integral over `U`. -/
theorem inner_wm_restrict_eq {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {U : Set (St d)} (hU : MeasurableSet U) (a b : Lp ℝ 2 ((wm w).restrict U)) :
    inner ℝ a b = ∫ x in U, w x * a x * b x := by
  rw [L2.inner_def]
  show ∫ x in U, inner ℝ (a x) (b x) ∂(volume.withDensity (fun x => ENNReal.ofReal (w x))) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul (f := fun x => ENNReal.ofReal (w x))
    (ENNReal.measurable_ofReal.comp hw.measurable)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) _ hU]
  refine setIntegral_congr_fun hU fun x _ => ?_
  have hreal : inner ℝ (a x) (b x) = (b x) * (a x) := by
    rw [RCLike.inner_apply]
    simp [mul_comm]
  simp only [hreal, ENNReal.toReal_ofReal (hpos x).le, smul_eq_mul]
  ring

/-- `E₁` is quasi-additive. -/
theorem energyNormSq_add_le {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {x y : Lp ℝ 2 (wm ρ)}
    (hx : x ∈ gradDomain hc hρ) (hy : y ∈ gradDomain hc hρ) :
    (gradClosedForm hc hρ hcpos hρpos).energyNormSq (x + y) ≤
      2 * (gradClosedForm hc hρ hcpos hρpos).energyNormSq x +
        2 * (gradClosedForm hc hρ hcpos hρpos).energyNormSq y := by
  set E := gradClosedForm hc hρ hcpos hρpos with hE
  have hx' : x ∈ E.domain := hx
  have hy' : y ∈ E.domain := hy
  unfold DirichletForm.ClosedForm.energyNormSq
  have h1 := E.form_add_self hx' hy'
  have h2 := E.form_nonneg (x - y) (E.domain.sub_mem hx' hy')
  have h3 : E.form (x - y) (x - y) = E.form x x - 2 * E.form x y + E.form y y := by
    have := E.form_add_self hx' (E.domain.neg_mem hy')
    rw [E.form_neg_right hx' hy', E.form_neg_left hy' (E.domain.neg_mem hy'),
      E.form_neg_right hy' hy'] at this
    rw [sub_eq_add_neg]
    linarith
  have h4 := norm_add_le x y
  have h5 : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg (x + y)) h4 2, sq_nonneg (‖x‖ - ‖y‖)]
  linarith

/-- Energy convergence from convergence of the graph coordinates. -/
theorem tendsto_energy_of_graph {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {z : Lp ℝ 2 (wm ρ)}
    (hz : z ∈ gradDomain hc hρ) {φ : ℕ → St d → ℝ} {hφ : ∀ n, φ n ∈ testFns d}
    (h1 : Tendsto (fun n => tcls hρ (φ n) (hφ n)) atTop (𝓝 z))
    (h2 : ∀ i, Tendsto (fun n => gcls hc (φ n) (hφ n) i) atTop (𝓝 (gradOf hc hρ z i))) :
    Tendsto (fun n => (gradClosedForm hc hρ hcpos hρpos).energyNormSq
      (z - tcls hρ (φ n) (hφ n))) atTop (𝓝 0) := by
  have hform : ∀ k, (gradClosedForm hc hρ hcpos hρpos).energyNormSq
      (z - tcls hρ (φ k) (hφ k)) =
      ∑ i, ‖gradOf hc hρ z i - gcls hc (φ k) (hφ k) i‖ ^ 2 +
        ‖z - tcls hρ (φ k) (hφ k)‖ ^ 2 := fun k =>
    energyNormSq_sub_test hc hρ hcpos hρpos hz (hφ k)
  have hA : ∀ i, Tendsto (fun k => ‖gradOf hc hρ z i - gcls hc (φ k) (hφ k) i‖ ^ 2)
      atTop (𝓝 0) := by
    intro i
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 (h2 i)).pow 2)
    rw [zero_pow (by norm_num)] at this
    exact this.congr fun k => by rw [norm_sub_rev]
  have hB : Tendsto (fun k => ‖z - tcls hρ (φ k) (hφ k)‖ ^ 2) atTop (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 h1).pow 2)
    rw [zero_pow (by norm_num)] at this
    exact this.congr fun k => by rw [norm_sub_rev]
  have := (tendsto_finset_sum Finset.univ fun i _ => hA i).add hB
  simpa [hform] using! this

/-- Graph convergence from energy convergence. -/
theorem graph_tendsto_of_energy {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {z : Lp ℝ 2 (wm ρ)}
    (hz : z ∈ gradDomain hc hρ) {φ : ℕ → St d → ℝ} {hφ : ∀ n, φ n ∈ testFns d}
    (hen : Tendsto (fun n => (gradClosedForm hc hρ hcpos hρpos).energyNormSq
      (z - tcls hρ (φ n) (hφ n))) atTop (𝓝 0)) :
    Tendsto (fun n => tcls hρ (φ n) (hφ n)) atTop (𝓝 z) ∧
      ∀ i, Tendsto (fun n => gcls hc (φ n) (hφ n) i) atTop (𝓝 (gradOf hc hρ z i)) := by
  have hform : ∀ k, (gradClosedForm hc hρ hcpos hρpos).energyNormSq
      (z - tcls hρ (φ k) (hφ k)) =
      ∑ i, ‖gradOf hc hρ z i - gcls hc (φ k) (hφ k) i‖ ^ 2 +
        ‖z - tcls hρ (φ k) (hφ k)‖ ^ 2 := fun k =>
    energyNormSq_sub_test hc hρ hcpos hρpos hz (hφ k)
  have hsqrt : ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) →
      (∀ n, a n ^ 2 ≤ (gradClosedForm hc hρ hcpos hρpos).energyNormSq
        (z - tcls hρ (φ n) (hφ n))) → Tendsto a atTop (𝓝 0) := by
    intro a ha hle
    have h0 := (Real.continuous_sqrt.tendsto 0).comp hen
    rw [Real.sqrt_zero] at h0
    refine squeeze_zero ha (fun n => ?_) h0
    calc a n = Real.sqrt (a n ^ 2) := (Real.sqrt_sq (ha n)).symm
      _ ≤ Real.sqrt _ := Real.sqrt_le_sqrt (hle n)
  refine ⟨?_, fun i => ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine (hsqrt (fun n => ‖z - tcls hρ (φ n) (hφ n)‖) (fun n => norm_nonneg _)
      (fun n => ?_)).congr fun n => norm_sub_rev _ _
    rw [hform]
    have : 0 ≤ ∑ i, ‖gradOf hc hρ z i - gcls hc (φ n) (hφ n) i‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine (hsqrt (fun n => ‖gradOf hc hρ z i - gcls hc (φ n) (hφ n) i‖)
      (fun n => norm_nonneg _) (fun n => ?_)).congr fun n => norm_sub_rev _ _
    rw [hform]
    have h1 : ‖gradOf hc hρ z i - gcls hc (φ n) (hφ n) i‖ ^ 2 ≤
        ∑ j, ‖gradOf hc hρ z j - gcls hc (φ n) (hφ n) j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖gradOf hc hρ z j - gcls hc (φ n) (hφ n) j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 := sq_nonneg ‖z - tcls hρ (φ n) (hφ n)‖
    linarith

theorem exists_test_supported_energy {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {U : Set (St d)} (hU : IsOpen U)
    {z : Lp ℝ 2 (wm ρ)} (hz : z ∈ gradDomain hc hρ)
    (hcore : DirichletForm.HasCoreRep (wm ρ) U z) :
    ∃ (ψ : ℕ → St d → ℝ) (hψ : ∀ n, ψ n ∈ testFns d), (∀ n, tsupport (ψ n) ⊆ U) ∧
      Tendsto (fun n => (gradClosedForm hc hρ hcpos hρpos).energyNormSq
        (z - tcls hρ (ψ n) (hψ n))) atTop (𝓝 0) := by
  obtain ⟨ψ, hψ, hs, h1, h2⟩ := exists_test_approx_supported hc hρ hcpos hρpos hU hz hcore
  exact ⟨ψ, hψ, hs, tendsto_energy_of_graph hc hρ hcpos hρpos hz h1 h2⟩

/-- Diagonal approximation: an energy-norm limit of core functions supported in `U` is an energy-norm
limit of test functions supported in `U`. -/
theorem exists_test_supported_of_core_limit {c ρ : St d → ℝ} (hc : Continuous c)
    (hρ : Continuous ρ) (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {U : Set (St d)}
    (hU : IsOpen U) {u : Lp ℝ 2 (wm ρ)} (hu : u ∈ gradDomain hc hρ) {w : ℕ → Lp ℝ 2 (wm ρ)}
    (hw : ∀ n, (gradClosedForm hc hρ hcpos hρpos).MemCoreOn U (w n))
    (hlim : Tendsto (fun n => (gradClosedForm hc hρ hcpos hρpos).energyNormSq (u - w n))
      atTop (𝓝 0)) :
    ∃ (ψ : ℕ → St d → ℝ) (hψ : ∀ n, ψ n ∈ testFns d), (∀ n, tsupport (ψ n) ⊆ U) ∧
      Tendsto (fun n => (gradClosedForm hc hρ hcpos hρpos).energyNormSq
        (u - tcls hρ (ψ n) (hψ n))) atTop (𝓝 0) := by
  have hex : ∀ n : ℕ, ∃ (ψ : St d → ℝ) (hψ : ψ ∈ testFns d), tsupport ψ ⊆ U ∧
      (gradClosedForm hc hρ hcpos hρpos).energyNormSq (w n - tcls hρ ψ hψ) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨ψ, hψ, hs, hten⟩ := exists_test_supported_energy hc hρ hcpos hρpos hU (hw n).1
      (hw n).2
    obtain ⟨k, hk⟩ := (hten.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by
      positivity))).exists
    exact ⟨ψ k, hψ k, hs k, hk⟩
  choose ψ hψ hs hlt using hex
  refine ⟨ψ, hψ, hs, ?_⟩
  have hup : ∀ n, (gradClosedForm hc hρ hcpos hρpos).energyNormSq (u - tcls hρ (ψ n) (hψ n)) ≤
      2 * (gradClosedForm hc hρ hcpos hρpos).energyNormSq (u - w n) + 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hsum : u - tcls hρ (ψ n) (hψ n) = (u - w n) + (w n - tcls hρ (ψ n) (hψ n)) := by abel
    rw [hsum]
    have := energyNormSq_add_le hc hρ hcpos hρpos
      ((gradDomain hc hρ).sub_mem hu (hw n).1)
      ((gradDomain hc hρ).sub_mem (hw n).1 (tcls_mem_gradDomain hc hρ (hψ n)))
    linarith [hlt n]
  have hlow : ∀ n, 0 ≤ (gradClosedForm hc hρ hcpos hρpos).energyNormSq
      (u - tcls hρ (ψ n) (hψ n)) := fun n => by
    unfold DirichletForm.ClosedForm.energyNormSq
    exact add_nonneg ((gradClosedForm hc hρ hcpos hρpos).form_nonneg _
      ((gradDomain hc hρ).sub_mem hu (tcls_mem_gradDomain hc hρ (hψ n)))) (sq_nonneg _)
  have hlim2 : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using! tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  refine squeeze_zero hlow hup ?_
  simpa using! (hlim.const_mul 2).add hlim2


theorem dpartial_const_mul {ψ : St d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (a : ℝ) (i : Fin d) :
    dpartial i (fun x => a * ψ x) = fun x => a * dpartial i ψ x := by
  have := dpartial_mul (contDiff_const (c := a)) hψ i
  rw [this]
  funext x
  simp [dpartial]

/-- The resolvent of the part form is `H¹`-approximable by `C_c^∞(U)` functions. -/
theorem boundaryApproximation_of_part {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {U : Set (St d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {u : Lp ℝ 2 (wm ρ)} (hu : u ∈ gradDomain hc hρ)
    {w : ℕ → Lp ℝ 2 (wm ρ)}
    (hw : ∀ n, (gradClosedForm hc hρ hcpos hρpos).MemCoreOn U (w n))
    (hlim : Tendsto (fun n => (gradClosedForm hc hρ hcpos hρpos).energyNormSq (u - w n))
      atTop (𝓝 0)) (a : ℝ) :
    Nonempty (SubdiffusiveProcess.Probability.Diffusion.Input.BoundaryApproximation U (fun x => a * u x)
      (fun x i => a * gradOf hc hρ u i x)) := by
  obtain ⟨ψ, hψ, hs, hen⟩ := exists_test_supported_of_core_limit hc hρ hcpos hρpos hU hu hw hlim
  obtain ⟨h1, h2⟩ := graph_tendsto_of_energy hc hρ hcpos hρpos hu hen
  have ha1 := tendsto_eLpNorm_tcls hρ h1
  have ha2 := fun i => tendsto_eLpNorm_gcls hc (h2 i)
  obtain ⟨C1, hC1, hle1⟩ := eLpNorm_restrict_le_wm hρ hρpos hU.measurableSet hUb
  obtain ⟨C2, hC2, hle2⟩ := eLpNorm_restrict_le_wm hc hcpos hU.measurableSet hUb
  refine ⟨{ memLp := (memLp_restrict_of_wm hρ hρpos hU.measurableSet hUb (Lp.memLp u)).const_mul a
            grad_memLp := fun i => (memLp_restrict_of_wm hc hcpos hU.measurableSet hUb
              (Lp.memLp (gradOf hc hρ u i))).const_mul a
            approx := fun n x => a * ψ n x
            smooth := fun n => contDiff_const.mul (hψ n).1
            compactSupport := fun n => (hψ n).2.mul_left (f := fun _ => a)
            support_subset := fun n => (tsupport_mul_subset_right (f := fun _ => a)
              (g := ψ n)).trans (hs n)
            tendsto_fun := ?_
            tendsto_grad := ?_ }⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (g := fun _ => (0 : ℝ≥0∞))
      (h := fun n => ‖a‖ₑ * C1 * eLpNorm (fun x => ψ n x - u x) 2 (wm ρ)) ?_
      (fun _ => zero_le) (fun n => ?_)
    · simpa using! ENNReal.Tendsto.const_mul ha1 (Or.inr (ENNReal.mul_ne_top enorm_ne_top hC1))
    · calc eLpNorm (fun x => a * ψ n x - a * u x) 2 (volume.restrict U)
          = ‖a‖ₑ * eLpNorm (fun x => ψ n x - u x) 2 (volume.restrict U) := by
            rw [show (fun x => a * ψ n x - a * u x) = a • (fun x => ψ n x - u x) from by
              funext x; simp [mul_sub], eLpNorm_const_smul]
        _ ≤ ‖a‖ₑ * (C1 * eLpNorm (fun x => ψ n x - u x) 2 (wm ρ)) := by
            gcongr
            exact hle1 _
        _ = ‖a‖ₑ * C1 * eLpNorm (fun x => ψ n x - u x) 2 (wm ρ) := by ring
  · intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (g := fun _ => (0 : ℝ≥0∞))
      (h := fun n => ‖a‖ₑ * C2 * eLpNorm (fun x => dpartial i (ψ n) x - gradOf hc hρ u i x) 2
        (wm c)) ?_ (fun _ => zero_le) (fun n => ?_)
    · simpa using! ENNReal.Tendsto.const_mul (ha2 i) (Or.inr (ENNReal.mul_ne_top enorm_ne_top hC2))
    · have hd := dpartial_const_mul (hψ n).1 a i
      calc eLpNorm (fun x => (fderiv ℝ (fun x => a * ψ n x) x) (Pi.single i 1) -
            a * gradOf hc hρ u i x) 2 (volume.restrict U)
          = eLpNorm (fun x => a * (dpartial i (ψ n) x - gradOf hc hρ u i x)) 2
              (volume.restrict U) := by
            refine eLpNorm_congr_ae (Eventually.of_forall fun x => ?_)
            have := congrFun hd x
            simp only [dpartial] at this ⊢
            rw [this]
            ring
        _ = ‖a‖ₑ * eLpNorm (fun x => dpartial i (ψ n) x - gradOf hc hρ u i x) 2
              (volume.restrict U) := by
            rw [show (fun x => a * (dpartial i (ψ n) x - gradOf hc hρ u i x)) =
              a • (fun x => dpartial i (ψ n) x - gradOf hc hρ u i x) from rfl, eLpNorm_const_smul]
        _ ≤ ‖a‖ₑ * (C2 * eLpNorm (fun x => dpartial i (ψ n) x - gradOf hc hρ u i x) 2 (wm c)) := by
            gcongr
            exact hle2 _
        _ = _ := by ring


theorem ae_vol_restrict_of_ae_wm_restrict {w : St d → ℝ} (hw : Continuous w)
    (hpos : ∀ x, 0 < w x) {U : Set (St d)} (hU : MeasurableSet U) {p : St d → Prop}
    (h : ∀ᵐ x ∂((wm w).restrict U), p x) : ∀ᵐ x ∂(volume.restrict U), p x := by
  rw [ae_iff] at h ⊢
  rw [Measure.restrict_apply' hU] at h ⊢
  exact (wm_null_iff hw hpos _).1 h

/-- **The weak equation of the part resolvent.** -/
theorem weak_eq_of_part {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {U : Set (St d)} (hU : IsOpen U)
    (F : DirichletForm.ClosedForm ((wm ρ).restrict U))
    (hpart : IsPartFormOn (gradClosedForm hc hρ hcpos hρpos) U F) {α : ℝ}
    (G : Lp ℝ 2 ((wm ρ).restrict U) →L[ℝ] Lp ℝ 2 ((wm ρ).restrict U))
    (hG : DirichletForm.IsResolvent F α G) {f : St d → ℝ}
    (hf : MemLp f 2 ((wm ρ).restrict U)) {u : Lp ℝ 2 (wm ρ)}
    (hu' : IsCoreLimitOn (gradClosedForm hc hρ hcpos hρpos) U u)
    (hv : restrictLp U u = G (hf.toLp f)) (ψ : St d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    α * (∫ x in U, ρ x * u x * ψ x) +
        (∫ x in U, ∑ i, c x * gradOf hc hρ u i x * dpartial i ψ x) =
      ∫ x in U, ρ x * f x * ψ x := by
  set E := gradClosedForm hc hρ hcpos hρpos with hE
  have hu : u ∈ gradDomain hc hρ := hu'.1
  have hψt : ψ ∈ testFns d := ⟨hψ, hψc⟩
  have hUm := hU.measurableSet
  set φ := restrictLp U (tcls hρ ψ hψt) with hφdef
  have hψcl : IsCoreLimitOn E U (tcls hρ ψ hψt) := by
    refine ⟨tcls_mem_gradDomain hc hρ hψt, fun _ => tcls hρ ψ hψt, fun _ => ?_, ?_⟩
    · exact ⟨tcls_mem_gradDomain hc hρ hψt, ψ, hψ.continuous, hψc, hψU, MemLp.coeFn_toLp _⟩
    · simp only [sub_self]
      have h0 : E.energyNormSq (0 : Lp ℝ 2 (wm ρ)) = 0 := by
        unfold DirichletForm.ClosedForm.energyNormSq
        rw [E.form_zero_left E.domain.zero_mem]
        simp
      simp [h0]
  have hφ : φ ∈ F.domain := (hpart.mem_domain_iff _).2 ⟨tcls hρ ψ hψt, hψcl, rfl⟩
  have hvmem : restrictLp U u ∈ F.domain := by rw [hv]; exact hG.mem_domain _
  have heq := hG.eq (hf.toLp f) hφ
  rw [← hv] at heq
  have hform : F.form (restrictLp U u) φ = E.form u (tcls hρ ψ hψt) :=
    hpart.form_eq u (tcls hρ ψ hψt) hu' hψcl
  rw [hform] at heq
  -- the energy term
  have hdψ : ∀ i x, x ∉ U → dpartial i ψ x = 0 := by
    intro i x hx
    have : fderiv ℝ ψ x = 0 :=
      Function.notMem_support.mp fun hs => hx (hψU (support_fderiv_subset ℝ hs))
    simp [dpartial, this]
  have hEterm : E.form u (tcls hρ ψ hψt) =
      ∫ x in U, ∑ i, c x * gradOf hc hρ u i x * dpartial i ψ x := by
    show gradForm hc hρ u (tcls hρ ψ hψt) = _
    unfold gradForm
    rw [gradOf_tcls hc hρ hcpos hρpos hψt]
    have hint : ∀ i ∈ Finset.univ, IntegrableOn
        (fun x => c x * gradOf hc hρ u i x * dpartial i ψ x) U volume := by
      intro i _
      have hi := integrable_wm_mul hc hcpos (gradOf hc hρ u i) (gcls hc ψ hψt i)
      have hae : ∀ᵐ x ∂(volume : Measure (St d)), (gcls hc ψ hψt i) x = dpartial i ψ x :=
        ae_volume_of_ae_wm hc hcpos (MemLp.coeFn_toLp _)
      refine (hi.congr ?_).integrableOn
      filter_upwards [hae] with x hx
      rw [hx]
    have hfull : ∀ i, inner ℝ (gradOf hc hρ u i) (gcls hc ψ hψt i) =
        ∫ x in U, c x * gradOf hc hρ u i x * dpartial i ψ x := by
      intro i
      rw [inner_wm_eq hc hcpos]
      have hae : ∀ᵐ x ∂(volume : Measure (St d)), (gcls hc ψ hψt i) x = dpartial i ψ x :=
        ae_volume_of_ae_wm hc hcpos (MemLp.coeFn_toLp _)
      rw [← integral_indicator hUm]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
      by_cases hxU : x ∈ U
      · simp [hxU]
      · simp [hxU, hdψ i x hxU]
    refine (Finset.sum_congr rfl fun i _ => hfull i).trans ?_
    rw [integral_finset_sum _ hint]
  -- the mass terms
  have hae_u : ∀ᵐ x ∂(volume.restrict U), (restrictLp U u) x = u x :=
    ae_vol_restrict_of_ae_wm_restrict hρ hρpos hUm (MemLp.coeFn_toLp _)
  have hae_φ : ∀ᵐ x ∂(volume.restrict U), φ x = ψ x := by
    have h1 := ae_vol_restrict_of_ae_wm_restrict hρ hρpos hUm
      (p := fun x => φ x = tcls hρ ψ hψt x) (MemLp.coeFn_toLp _)
    have h2 : ∀ᵐ x ∂(volume : Measure (St d)), (tcls hρ ψ hψt) x = ψ x :=
      ae_volume_of_ae_wm hρ hρpos (MemLp.coeFn_toLp _)
    filter_upwards [h1, ae_restrict_of_ae h2] with x hx1 hx2
    rw [hx1, hx2]
  have hae_f : ∀ᵐ x ∂(volume.restrict U), (hf.toLp f) x = f x :=
    ae_vol_restrict_of_ae_wm_restrict hρ hρpos hUm hf.coeFn_toLp
  have hm1 : inner ℝ (restrictLp U u) φ = ∫ x in U, ρ x * u x * ψ x := by
    rw [inner_wm_restrict_eq hρ hρpos hUm]
    refine integral_congr_ae ?_
    filter_upwards [hae_u, hae_φ] with x h1 h2
    rw [h1, h2]
  have hm2 : inner ℝ (hf.toLp f) φ = ∫ x in U, ρ x * f x * ψ x := by
    rw [inner_wm_restrict_eq hρ hρpos hUm]
    refine integral_congr_ae ?_
    filter_upwards [hae_f, hae_φ] with x h1 h2
    rw [h1, h2]
  rw [hm1, hEterm, hm2] at heq
  exact heq


theorem integrableOn_wm_restrict_mul {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {U : Set (St d)} (hU : MeasurableSet U) (a b : Lp ℝ 2 ((wm w).restrict U)) :
    IntegrableOn (fun x => w x * a x * b x) U volume := by
  have h1 : Integrable (fun x => inner ℝ (a x) (b x)) ((wm w).restrict U) := L2.integrable_inner a b
  have hreal : ∀ x, inner ℝ (a x) (b x) = (b x) * (a x) := fun x => by
    rw [RCLike.inner_apply]
    simp [mul_comm]
  obtain ⟨g, hg⟩ : ∃ g : St d → ℝ, g = fun x => (b : St d → ℝ) x * (a : St d → ℝ) x := ⟨_, rfl⟩
  have h1' : Integrable g ((wm w).restrict U) := by
    rw [hg]
    exact h1.congr (Eventually.of_forall fun x => hreal x)
  have hm : (wm w).restrict U = (volume.restrict U).withDensity (fun x => ENNReal.ofReal (w x)) :=
    restrict_withDensity hU _
  rw [hm] at h1'
  have h2 := (integrable_withDensity_iff_integrable_smul' (μ := volume.restrict U)
    (f := fun x => ENNReal.ofReal (w x)) (ENNReal.measurable_ofReal.comp hw.measurable)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).1 h1'
  refine h2.congr (Eventually.of_forall fun x => ?_)
  simp only [hg, ENNReal.toReal_ofReal (hpos x).le, smul_eq_mul]
  ring

/-- **The analytic content of the killed-generator identification.** -/
theorem part_analytic {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {U : Set (St d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (F : DirichletForm.ClosedForm ((wm ρ).restrict U))
    (hpart : IsPartFormOn (gradClosedForm hc hρ hcpos hρpos) U F) {α : ℝ}
    (G : Lp ℝ 2 ((wm ρ).restrict U) →L[ℝ] Lp ℝ 2 ((wm ρ).restrict U))
    (hG : DirichletForm.IsResolvent F α G) {f : St d → ℝ}
    (hf : MemLp f 2 ((wm ρ).restrict U)) :
    ∃ (u : St d → ℝ) (Du : St d → St d),
      Nonempty (SubdiffusiveProcess.Probability.Diffusion.Input.BoundaryApproximation U u Du) ∧
      (u =ᵐ[(wm ρ).restrict U] fun x => α * (G (hf.toLp f)) x) ∧
      ∀ ψ : St d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        (∫ x in U, ∑ i, (c x * Du x i) * (fderiv ℝ ψ x) (Pi.single i 1)) =
          ∫ x in U, (ρ x * (α * (f x - u x))) * ψ x := by
  have hUm := hU.measurableSet
  have hvmem : G (hf.toLp f) ∈ F.domain := hG.mem_domain _
  obtain ⟨ũ, ⟨hũ, w, hw, hlim⟩, hũv⟩ := (hpart.mem_domain_iff _).1 hvmem
  refine ⟨fun x => α * ũ x, fun x i => α * gradOf hc hρ ũ i x,
    boundaryApproximation_of_part hc hρ hcpos hρpos hU hUb hũ hw hlim α, ?_, ?_⟩
  · have h1 : ∀ᵐ x ∂((wm ρ).restrict U), (restrictLp U ũ) x = ũ x := MemLp.coeFn_toLp _
    filter_upwards [h1] with x hx
    rw [← hũv, hx]
  · intro ψ hψ hψc hψU
    have hweak := weak_eq_of_part hc hρ hcpos hρpos hU F hpart G hG hf ⟨hũ, w, hw, hlim⟩ hũv ψ hψ hψc hψU
    have hψt : ψ ∈ testFns d := ⟨hψ, hψc⟩
    -- integrability
    have hI1 : IntegrableOn (fun x => ρ x * ũ x * ψ x) U volume := by
      have hi := integrable_wm_mul hρ hρpos ũ (tcls hρ ψ hψt)
      have hae : ∀ᵐ x ∂(volume : Measure (St d)), (tcls hρ ψ hψt) x = ψ x :=
        ae_volume_of_ae_wm hρ hρpos (MemLp.coeFn_toLp _)
      refine (hi.congr ?_).integrableOn
      filter_upwards [hae] with x hx
      rw [hx]
    have hI2 : IntegrableOn (fun x => ρ x * f x * ψ x) U volume := by
      have hi := integrableOn_wm_restrict_mul hρ hρpos hUm (hf.toLp f)
        (restrictLp U (tcls hρ ψ hψt))
      have h1 : ∀ᵐ x ∂(volume.restrict U), (hf.toLp f) x = f x :=
        ae_vol_restrict_of_ae_wm_restrict hρ hρpos hUm hf.coeFn_toLp
      have h2 : ∀ᵐ x ∂(volume.restrict U), (restrictLp U (tcls hρ ψ hψt)) x = ψ x := by
        have h3 := ae_vol_restrict_of_ae_wm_restrict hρ hρpos hUm
          (p := fun x => (restrictLp U (tcls hρ ψ hψt)) x = tcls hρ ψ hψt x)
          (MemLp.coeFn_toLp _)
        have h4 : ∀ᵐ x ∂(volume : Measure (St d)), (tcls hρ ψ hψt) x = ψ x :=
          ae_volume_of_ae_wm hρ hρpos (MemLp.coeFn_toLp _)
        filter_upwards [h3, ae_restrict_of_ae h4] with x hx1 hx2
        rw [hx1, hx2]
      refine hi.congr ?_
      filter_upwards [h1, h2] with x hx1 hx2
      rw [hx1, hx2]
    have hL : (∫ x in U, ∑ i, (c x * (α * gradOf hc hρ ũ i x)) * (fderiv ℝ ψ x) (Pi.single i 1)) =
        α * ∫ x in U, ∑ i, c x * gradOf hc hρ ũ i x * dpartial i ψ x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [dpartial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hR : (∫ x in U, (ρ x * (α * (f x - α * ũ x))) * ψ x) =
        α * (∫ x in U, ρ x * f x * ψ x) - α * (α * ∫ x in U, ρ x * ũ x * ψ x) := by
      have h1 : (fun x => ρ x * (α * (f x - α * ũ x)) * ψ x) =
          fun x => α * (ρ x * f x * ψ x) - (α * α) * (ρ x * ũ x * ψ x) := by
        funext x; ring
      rw [h1, integral_sub (hI2.const_mul α) (hI1.const_mul (α * α)), integral_const_mul,
        integral_const_mul]
      ring
    rw [hL, hR]
    linear_combination α * hweak

end SubdiffusiveProcess.E7
