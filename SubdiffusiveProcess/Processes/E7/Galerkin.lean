import SubdiffusiveProcess.Processes.E7.GradMarkov
import Homogenization.Sobolev.W1p.ZeroExtensionGraph
import Homogenization.Sobolev.H1.Definitions
import Homogenization.Sobolev.H1.Algebra.H10Function

/-!
# Zero-extended `H¹₀` functions in the form domain, and Galerkin approximation

For a bounded open set `W`, the zero extension of an `H¹₀(W)` function lies in the domain of the
gradient form, with gradient the zero extension of its gradient. The variational solutions on an
exhausting family of sets are Galerkin approximations of the resolvent of the form: by Céa's lemma
they converge to it in `L²(ρ)`.
-/
open MeasureTheory Filter Set Topology Homogenization
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- The inner product of `L²(w dx)` as a Lebesgue integral. -/
theorem inner_wm_eq {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (a b : Lp ℝ 2 (wm w)) : inner ℝ a b = ∫ x, w x * a x * b x := by
  rw [L2.inner_def]
  have step2 : ∫ x, inner ℝ (a x) (b x) ∂wm w
      = ∫ x, (ENNReal.ofReal (w x)).toReal • inner ℝ (a x) (b x) ∂volume := by
    show ∫ x, inner ℝ (a x) (b x) ∂volume.withDensity (fun x => ENNReal.ofReal (w x)) = _
    exact integral_withDensity_eq_integral_toReal_smul
      (ENNReal.measurable_ofReal.comp hw.measurable)
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))
      (fun x => inner ℝ (a x) (b x))
  rw [step2]
  apply integral_congr_ae
  filter_upwards with x
  have hreal : inner ℝ (a x) (b x) = (b x) * (a x) := by
    rw [RCLike.inner_apply]
    simp [mul_comm]
  rw [hreal, ENNReal.toReal_ofReal (hpos x).le, smul_eq_mul]
  ring

/-- Products of `L²(w dx)` classes are integrable against `w dx` in Lebesgue form. -/
theorem integrable_wm_mul {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (a b : Lp ℝ 2 (wm w)) : Integrable (fun x => w x * a x * b x) volume := by
  have h1 : Integrable (fun x => inner ℝ (a x) (b x)) (wm w) := L2.integrable_inner a b
  have h2 := (integrable_withDensity_iff_integrable_smul' (μ := volume)
    (f := fun x => ENNReal.ofReal (w x)) (ENNReal.measurable_ofReal.comp hw.measurable)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).1 h1
  refine h2.congr (Eventually.of_forall fun x => ?_)
  have hreal : inner ℝ (a x) (b x) = (b x) * (a x) := by
    rw [RCLike.inner_apply]
    simp [mul_comm]
  simp only [hreal, ENNReal.toReal_ofReal (hpos x).le, smul_eq_mul]
  ring

/-- `wm w` on a measurable bounded set is dominated by a multiple of Lebesgue measure. -/
theorem wm_restrict_le_smul {w : St d → ℝ} (hw : Continuous w) {W : Set (St d)}
    (hW : MeasurableSet W) (hWb : Bornology.IsBounded W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (wm w).restrict W ≤ C • (volume : Measure (St d)).restrict W := by
  obtain ⟨M, hM⟩ := hWb.isCompact_closure.exists_bound_of_continuousOn hw.continuousOn
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_ne_top, ?_⟩
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, wm,
    withDensity_apply _ (hs.inter hW)]
  calc ∫⁻ x in s ∩ W, ENNReal.ofReal (w x)
      ≤ ∫⁻ x in s ∩ W, ENNReal.ofReal M := by
        refine setLIntegral_mono' (hs.inter hW) (fun x hx => ENNReal.ofReal_le_ofReal ?_)
        exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hM x (subset_closure hx.2))
    _ = ENNReal.ofReal M * volume (s ∩ W) := setLIntegral_const _ _

/-- An `L²(w dx)` bound for functions supported in a measurable bounded set `W`, in terms of the
Lebesgue `L²(W)` norm. -/
theorem eLpNorm_wm_le {w : St d → ℝ} (hw : Continuous w) {W : Set (St d)}
    (hW : MeasurableSet W) (hWb : Bornology.IsBounded W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : St d → ℝ, (∀ x, x ∉ W → f x = 0) →
      eLpNorm f 2 (wm w) ≤ C * eLpNorm f 2 (volume.restrict W) := by
  obtain ⟨C0, hC0, hle⟩ := wm_restrict_le_smul hw hW hWb
  refine ⟨C0 ^ (1 / (2 : ℝ)), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC0, fun f hf => ?_⟩
  have hfeq : f = W.indicator f := by
    funext x
    by_cases hx : x ∈ W
    · simp [hx]
    · simp [hx, hf x hx]
  calc eLpNorm f 2 (wm w) = eLpNorm (W.indicator f) 2 (wm w) := by rw [← hfeq]
    _ = eLpNorm f 2 ((wm w).restrict W) := eLpNorm_indicator_eq_eLpNorm_restrict hW
    _ ≤ eLpNorm f 2 (C0 • (volume : Measure (St d)).restrict W) := eLpNorm_mono_measure _ hle
    _ = C0 ^ (1 / (2 : ℝ)) * eLpNorm f 2 (volume.restrict W) := by
        rw [eLpNorm_smul_measure_of_ne_top (by norm_num)]
        simp

theorem memLp_zeroExt_wm {ρ : St d → ℝ} (hρ : Continuous ρ) {W : Set (Vec d)}
    (hW : IsOpen W) (hWb : Bornology.IsBounded W) (v : H10Function W) :
    MemLp v.zeroExtension 2 (wm ρ) := by
  obtain ⟨C, hC, hle⟩ := wm_restrict_le_smul hρ hW.measurableSet hWb
  refine (memLp_indicator_iff_restrict hW.measurableSet).2 ?_
  exact MemLp.of_measure_le_smul hC hle v.toH1Function.memL2

theorem memLp_zeroExtGrad_wm {c : St d → ℝ} (hc : Continuous c) {W : Set (Vec d)}
    (hW : IsOpen W) (hWb : Bornology.IsBounded W) (v : H10Function W) (i : Fin d) :
    MemLp (fun x => v.zeroExtensionGrad x i) 2 (wm c) := by
  obtain ⟨C, hC, hle⟩ := wm_restrict_le_smul hc hW.measurableSet hWb
  have hfun : (fun x => v.zeroExtensionGrad x i) =
      W.indicator (fun x => v.toH1Function.grad x i) := by
    funext x
    by_cases hx : x ∈ W
    · simp [H10Function.zeroExtensionGrad_apply_of_mem v hx, hx]
    · simp [H10Function.zeroExtensionGrad_apply_of_not_mem v hx, hx]
  rw [hfun]
  refine (memLp_indicator_iff_restrict hW.measurableSet).2 ?_
  exact MemLp.of_measure_le_smul hC hle (v.toH1Function.gradMemL2 i)

/-- The `L²(ρ)` class of the zero extension of an `H¹₀(W)` function. -/
def zextL {ρ : St d → ℝ} (hρ : Continuous ρ) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (v : H10Function W) : Lp ℝ 2 (wm ρ) :=
  (memLp_zeroExt_wm hρ hW hWb v).toLp v.zeroExtension

/-- The `L²(c)` class of a component of the zero-extended gradient. -/
def zextG {c : St d → ℝ} (hc : Continuous c) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (v : H10Function W) (i : Fin d) : Lp ℝ 2 (wm c) :=
  (memLp_zeroExtGrad_wm hc hW hWb v i).toLp (fun x => v.zeroExtensionGrad x i)

/-- The zero extension with its gradient is a point of the closed graph. -/
theorem zext_mem_gradGraph {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (v : H10Function W) :
    (zextL hρ hW hWb v, fun i => zextG hc hW hWb v i) ∈ gradGraph hc hρ := by
  have hφ : ∀ n, v.approx n ∈ testFns d := fun n => ⟨v.approx_smooth n, v.approx_hasCompactSupport n⟩
  have hvanish : ∀ n x, x ∉ W → v.approx n x = 0 := fun n x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (v.approx_support_subset n h))
  have hdvanish : ∀ n i x, x ∉ W → dpartial i (v.approx n) x = 0 := by
    intro n i x hx
    have : fderiv ℝ (v.approx n) x = 0 :=
      Function.notMem_support.mp fun hs =>
        hx (v.approx_support_subset n (support_fderiv_subset ℝ hs))
    simp [dpartial, this]
  obtain ⟨C1, hC1, hle1⟩ := eLpNorm_wm_le hρ hW.measurableSet hWb
  obtain ⟨C2, hC2, hle2⟩ := eLpNorm_wm_le hc hW.measurableSet hWb
  refine mem_gradGraph_of_tendsto hc hρ v.approx hφ ?_ ?_
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hbound : ∀ n, eLpNorm (⇑(tcls hρ (v.approx n) (hφ n)) - ⇑(zextL hρ hW hWb v)) 2 (wm ρ) ≤
        C1 * eLpNorm (fun x => v.approx n x - v.toH1Function.toFun x) 2 (volume.restrict W) := by
      intro n
      have hae : (⇑(tcls hρ (v.approx n) (hφ n)) - ⇑(zextL hρ hW hWb v)) =ᵐ[wm ρ]
          fun x => v.approx n x - v.zeroExtension x := by
        filter_upwards [MemLp.coeFn_toLp (memLp_wm_of_test hρ (hφ n)),
          MemLp.coeFn_toLp (memLp_zeroExt_wm hρ hW hWb v)] with x h1 h2
        simp only [tcls, zextL, Pi.sub_apply, h1, h2]
      rw [eLpNorm_congr_ae hae]
      have := hle1 (fun x => v.approx n x - v.zeroExtension x) (fun x hx => by
        simp [hvanish n x hx, H10Function.zeroExtension_apply_of_not_mem v hx])
      refine this.trans ?_
      gcongr
      refine le_of_eq (eLpNorm_congr_ae ?_)
      filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
      simp [H10Function.zeroExtension_apply_of_mem v hx]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le _) hbound
    have := ENNReal.Tendsto.const_mul v.tendsto_approx (Or.inr hC1)
    simpa using this
  · intro i
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hbound : ∀ n, eLpNorm (⇑(gcls hc (v.approx n) (hφ n) i) - ⇑(zextG hc hW hWb v i)) 2 (wm c) ≤
        C2 * eLpNorm (fun x => (fderiv ℝ (v.approx n) x) (basisVec i) -
          v.toH1Function.grad x i) 2 (volume.restrict W) := by
      intro n
      have hae : (⇑(gcls hc (v.approx n) (hφ n) i) - ⇑(zextG hc hW hWb v i)) =ᵐ[wm c]
          fun x => dpartial i (v.approx n) x - v.zeroExtensionGrad x i := by
        filter_upwards [MemLp.coeFn_toLp (memLp_wm_dpartial hc (hφ n) i),
          MemLp.coeFn_toLp (memLp_zeroExtGrad_wm hc hW hWb v i)] with x h1 h2
        simp only [gcls, zextG, Pi.sub_apply, h1, h2]
      rw [eLpNorm_congr_ae hae]
      have := hle2 (fun x => dpartial i (v.approx n) x - v.zeroExtensionGrad x i) (fun x hx => by
        simp [hdvanish n i x hx, H10Function.zeroExtensionGrad_apply_of_not_mem v hx])
      refine this.trans ?_
      gcongr
      refine le_of_eq (eLpNorm_congr_ae ?_)
      filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
      simp [dpartial, basisVec, H10Function.zeroExtensionGrad_apply_of_mem v hx]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le _) hbound
    have := ENNReal.Tendsto.const_mul (v.tendsto_approx_grad i) (Or.inr hC2)
    simpa using this

theorem zextL_mem_gradDomain {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (v : H10Function W) :
    zextL hρ hW hWb v ∈ gradDomain hc hρ :=
  (mem_gradDomain_iff hc hρ _).2 ⟨_, zext_mem_gradGraph hc hρ hcpos hρpos hW hWb v⟩

theorem gradOf_zextL {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (v : H10Function W) :
    gradOf hc hρ (zextL hρ hW hWb v) = fun i => zextG hc hW hWb v i :=
  gradOf_spec hc hρ hcpos hρpos (zext_mem_gradGraph hc hρ hcpos hρpos hW hWb v)

/-- The inner product of a class in `L²(ρ)` against a zero-extended `H¹₀(W)` function. -/
theorem inner_zextL_eq {ρ : St d → ℝ} (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) (a : Lp ℝ 2 (wm ρ))
    (w : H10Function W) :
    inner ℝ a (zextL hρ hW hWb w) = ∫ x in W, ρ x * a x * w.toH1Function.toFun x := by
  rw [inner_wm_eq hρ hρpos, ← integral_indicator hW.measurableSet]
  have hae : ∀ᵐ x ∂(volume : Measure (St d)), (zextL hρ hW hWb w) x = w.zeroExtension x :=
    ae_volume_of_ae_wm hρ hρpos (MemLp.coeFn_toLp _)
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]
  by_cases hxW : x ∈ W
  · simp [hxW]
  · simp [hxW]

theorem integrableOn_zextL {ρ : St d → ℝ} (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) (a : Lp ℝ 2 (wm ρ))
    (w : H10Function W) :
    IntegrableOn (fun x => ρ x * a x * w.toH1Function.toFun x) W volume := by
  have hi := integrable_wm_mul hρ hρpos a (zextL hρ hW hWb w)
  have hae : ∀ᵐ x ∂(volume : Measure (St d)), (zextL hρ hW hWb w) x = w.zeroExtension x :=
    ae_volume_of_ae_wm hρ hρpos (MemLp.coeFn_toLp _)
  rw [← integrable_indicator_iff hW.measurableSet]
  refine hi.congr ?_
  filter_upwards [hae] with x hx
  rw [hx]
  by_cases hxW : x ∈ W
  · simp [hxW]
  · simp [hxW]

/-- The inner product of a gradient class in `L²(c)` against a zero-extended gradient component. -/
theorem inner_zextG_eq {c : St d → ℝ} (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) (b : Lp ℝ 2 (wm c))
    (w : H10Function W) (i : Fin d) :
    inner ℝ b (zextG hc hW hWb w i) = ∫ x in W, c x * b x * w.toH1Function.grad x i := by
  rw [inner_wm_eq hc hcpos, ← integral_indicator hW.measurableSet]
  have hae : ∀ᵐ x ∂(volume : Measure (St d)), (zextG hc hW hWb w i) x = w.zeroExtensionGrad x i :=
    ae_volume_of_ae_wm hc hcpos (MemLp.coeFn_toLp _)
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]
  by_cases hxW : x ∈ W
  · simp [hxW]
  · simp [hxW]

theorem integrableOn_zextG {c : St d → ℝ} (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) (b : Lp ℝ 2 (wm c))
    (w : H10Function W) (i : Fin d) :
    IntegrableOn (fun x => c x * b x * w.toH1Function.grad x i) W volume := by
  have hi := integrable_wm_mul hc hcpos b (zextG hc hW hWb w i)
  have hae : ∀ᵐ x ∂(volume : Measure (St d)), (zextG hc hW hWb w i) x = w.zeroExtensionGrad x i :=
    ae_volume_of_ae_wm hc hcpos (MemLp.coeFn_toLp _)
  rw [← integrable_indicator_iff hW.measurableSet]
  refine hi.congr ?_
  filter_upwards [hae] with x hx
  rw [hx]
  by_cases hxW : x ∈ W
  · simp [hxW]
  · simp [hxW]

theorem inner_zextL {ρ : St d → ℝ} (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) (v w : H10Function W) :
    inner ℝ (zextL hρ hW hWb v) (zextL hρ hW hWb w) =
      ∫ x in W, ρ x * v.toH1Function.toFun x * w.toH1Function.toFun x := by
  rw [inner_zextL_eq hρ hρpos hW hWb]
  refine setIntegral_congr_ae hW.measurableSet ?_
  have hae : ∀ᵐ x ∂(volume : Measure (St d)), (zextL hρ hW hWb v) x = v.zeroExtension x :=
    ae_volume_of_ae_wm hρ hρpos (MemLp.coeFn_toLp _)
  filter_upwards [hae] with x hx hxW
  rw [hx, H10Function.zeroExtension_apply_of_mem v hxW]

theorem inner_zextG {c : St d → ℝ} (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) (v w : H10Function W)
    (i : Fin d) :
    inner ℝ (zextG hc hW hWb v i) (zextG hc hW hWb w i) =
      ∫ x in W, c x * v.toH1Function.grad x i * w.toH1Function.grad x i := by
  rw [inner_zextG_eq hc hcpos hW hWb]
  refine setIntegral_congr_ae hW.measurableSet ?_
  have hae : ∀ᵐ x ∂(volume : Measure (St d)), (zextG hc hW hWb v i) x = v.zeroExtensionGrad x i :=
    ae_volume_of_ae_wm hc hcpos (MemLp.coeFn_toLp _)
  filter_upwards [hae] with x hx hxW
  rw [hx, H10Function.zeroExtensionGrad_apply_of_mem v hxW]

theorem gradForm_zext {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (v w : H10Function W) :
    gradForm hc hρ (zextL hρ hW hWb v) (zextL hρ hW hWb w) =
      ∫ x in W, vecDot (c x • v.toH1Function.grad x) (w.toH1Function.grad x) := by
  unfold gradForm
  simp_rw [gradOf_zextL hc hρ hcpos hρpos hW hWb, inner_zextG hc hcpos hW hWb]
  have hint : ∀ i ∈ Finset.univ, IntegrableOn
      (fun x => c x * v.toH1Function.grad x i * w.toH1Function.grad x i) W volume := by
    intro i _
    have h := integrableOn_zextG hc hcpos hW hWb (zextG hc hW hWb v i) w i
    refine h.congr_fun_ae ?_
    have hae : ∀ᵐ x ∂(volume : Measure (St d)), (zextG hc hW hWb v i) x = v.zeroExtensionGrad x i :=
      ae_volume_of_ae_wm hc hcpos (MemLp.coeFn_toLp _)
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hW.measurableSet] with x hx hxW
    rw [hx, H10Function.zeroExtensionGrad_apply_of_mem v hxW]
  rw [← integral_finset_sum _ hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [vecDot, mul_assoc]

theorem inner_toLp_zextL {ρ : St d → ℝ} (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) {f : St d → ℝ}
    (hf : MemLp f 2 (wm ρ)) (w : H10Function W) :
    inner ℝ (hf.toLp f) (zextL hρ hW hWb w) = ∫ x in W, ρ x * f x * w.toH1Function.toFun x := by
  rw [inner_zextL_eq hρ hρpos hW hWb]
  refine setIntegral_congr_ae hW.measurableSet ?_
  have hae : ∀ᵐ x ∂(volume : Measure (St d)), (hf.toLp f) x = f x :=
    ae_volume_of_ae_wm hρ hρpos hf.coeFn_toLp
  filter_upwards [hae] with x hx _
  rw [hx]

/-! ### The shifted form and Céa's lemma -/

/-- The shifted energy `E_μ(a, b) = μ ⟪a, b⟫ + E(a, b)`. -/
def emu {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ) (μ : ℝ)
    (a b : Lp ℝ 2 (wm ρ)) : ℝ := μ * inner ℝ a b + gradForm hc hρ a b

theorem emu_comm {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) (μ : ℝ) {a b : Lp ℝ 2 (wm ρ)}
    (ha : a ∈ gradDomain hc hρ) (hb : b ∈ gradDomain hc hρ) :
    emu hc hρ μ a b = emu hc hρ μ b a := by
  have h : gradForm hc hρ a b = gradForm hc hρ b a :=
    (gradClosedForm hc hρ hcpos hρpos).form_symm a ha b hb
  unfold emu
  rw [h, real_inner_comm a b]

theorem emu_sub_left {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) (μ : ℝ) {a b z : Lp ℝ 2 (wm ρ)}
    (ha : a ∈ gradDomain hc hρ) (hb : b ∈ gradDomain hc hρ) (hz : z ∈ gradDomain hc hρ) :
    emu hc hρ μ (a - b) z = emu hc hρ μ a z - emu hc hρ μ b z := by
  have h : gradForm hc hρ (a - b) z = gradForm hc hρ a z - gradForm hc hρ b z :=
    (gradClosedForm hc hρ hcpos hρpos).form_sub_left ha hb hz
  unfold emu
  rw [h, inner_sub_left]
  ring

theorem emu_self_nonneg {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {μ : ℝ} (hμ : 0 ≤ μ)
    {a : Lp ℝ 2 (wm ρ)} (ha : a ∈ gradDomain hc hρ) : 0 ≤ emu hc hρ μ a a := by
  have h : 0 ≤ gradForm hc hρ a a := (gradClosedForm hc hρ hcpos hρpos).form_nonneg a ha
  have h2 : 0 ≤ inner ℝ a a := real_inner_self_nonneg
  unfold emu
  exact add_nonneg (mul_nonneg hμ h2) h

/-- Cauchy–Schwarz for the shifted energy. -/
theorem emu_sq_le {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {μ : ℝ} (hμ : 0 ≤ μ)
    {a b : Lp ℝ 2 (wm ρ)} (ha : a ∈ gradDomain hc hρ) (hb : b ∈ gradDomain hc hρ) :
    emu hc hρ μ a b ^ 2 ≤ emu hc hρ μ a a * emu hc hρ μ b b := by
  have key : ∀ t : ℝ, 0 ≤ emu hc hρ μ b b * (t * t) + 2 * emu hc hρ μ a b * t +
      emu hc hρ μ a a := by
    intro t
    have hd : a + t • b ∈ gradDomain hc hρ :=
      (gradDomain hc hρ).add_mem ha ((gradDomain hc hρ).smul_mem t hb)
    have h := emu_self_nonneg hc hρ hcpos hρpos hμ hd
    have hE : gradForm hc hρ (a + t • b) (a + t • b) = gradForm hc hρ a a +
        2 * t * gradForm hc hρ a b + t ^ 2 * gradForm hc hρ b b :=
      (gradClosedForm hc hρ hcpos hρpos).form_add_smul_self t ha hb
    have hexp : emu hc hρ μ (a + t • b) (a + t • b) = emu hc hρ μ a a +
        2 * t * emu hc hρ μ a b + t ^ 2 * emu hc hρ μ b b := by
      unfold emu
      rw [hE]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm a b]
      ring
    nlinarith [h, hexp]
  have h := discrim_le_zero key
  rw [discrim] at h
  nlinarith [h]

theorem emu_self_le_energyNormSq {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {μ : ℝ} (hμ : 0 ≤ μ)
    (a : Lp ℝ 2 (wm ρ)) :
    emu hc hρ μ a a ≤ max μ 1 * (gradClosedForm hc hρ hcpos hρpos).energyNormSq a := by
  have hE : (gradClosedForm hc hρ hcpos hρpos).energyNormSq a = gradForm hc hρ a a + ‖a‖ ^ 2 := by
    unfold DirichletForm.ClosedForm.energyNormSq
    rfl
  have h1 : 0 ≤ gradForm hc hρ a a := by
    rw [gradForm_self]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold emu
  rw [hE, real_inner_self_eq_norm_sq]
  have h2 : (1 : ℝ) ≤ max μ 1 := le_max_right _ _
  have h3 : μ ≤ max μ 1 := le_max_left _ _
  nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖a‖),
    mul_le_mul_of_nonneg_right h2 h1]

theorem norm_sq_le_emu {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {μ : ℝ} (hμ : 0 < μ)
    {a : Lp ℝ 2 (wm ρ)} (ha : a ∈ gradDomain hc hρ) :
    μ * ‖a‖ ^ 2 ≤ emu hc hρ μ a a := by
  have h1 : 0 ≤ gradForm hc hρ a a := (gradClosedForm hc hρ hcpos hρpos).form_nonneg a ha
  unfold emu
  rw [real_inner_self_eq_norm_sq]
  linarith

theorem zextL_sub {ρ : St d → ℝ} (hρ : Continuous ρ) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (v w : H10Function W) :
    zextL hρ hW hWb (v - w) = zextL hρ hW hWb v - zextL hρ hW hWb w := by
  apply Lp.ext
  have hL : ∀ u : H10Function W, (⇑(zextL hρ hW hWb u)) =ᵐ[wm ρ] u.zeroExtension :=
    fun u => MemLp.coeFn_toLp _
  have hsub : ∀ x, (v - w).zeroExtension x = v.zeroExtension x - w.zeroExtension x := by
    intro x
    by_cases hx : x ∈ W
    · rw [H10Function.zeroExtension_apply_of_mem _ hx, H10Function.zeroExtension_apply_of_mem _ hx,
        H10Function.zeroExtension_apply_of_mem _ hx]
      change (v.toH1Function - w.toH1Function).toFun x = _
      rw [H1Function.sub_toFun]
    · simp [H10Function.zeroExtension_apply_of_not_mem _ hx]
  filter_upwards [hL (v - w), hL v, hL w, Lp.coeFn_sub (zextL hρ hW hWb v) (zextL hρ hW hWb w)]
    with x hx1 hx2 hx3 hx4
  rw [hx1, hx4, Pi.sub_apply, hx2, hx3]
  exact hsub x

/-- **Galerkin orthogonality**: the error of the `H¹₀(W)` variational solution is `E_μ`-orthogonal
to the zero extensions of `H¹₀(W)`. -/
theorem galerkin_orthogonal {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {μ : ℝ}
    {G : Lp ℝ 2 (wm ρ) →L[ℝ] Lp ℝ 2 (wm ρ)}
    (hG : DirichletForm.IsResolvent (gradClosedForm hc hρ hcpos hρpos) μ G)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) {f : St d → ℝ}
    (hf : MemLp f 2 (wm ρ)) (v : H10Function W)
    (hv : ∀ φ : H10Function W,
      μ * ∫ x in W, ρ x * v.toH1Function.toFun x * φ.toH1Function.toFun x ∂volume +
        ∫ x in W, vecDot (c x • v.toH1Function.grad x) (φ.toH1Function.grad x) ∂volume =
      ∫ x in W, ρ x * f x * φ.toH1Function.toFun x ∂volume)
    (φ : H10Function W) :
    emu hc hρ μ (G (hf.toLp f) - zextL hρ hW hWb v) (zextL hρ hW hWb φ) = 0 := by
  have hgd : G (hf.toLp f) ∈ gradDomain hc hρ := hG.mem_domain _
  have hz := zextL_mem_gradDomain hc hρ hcpos hρpos hW hWb φ
  have hzv := zextL_mem_gradDomain hc hρ hcpos hρpos hW hWb v
  rw [emu_sub_left hc hρ hcpos hρpos μ hgd hzv hz]
  have e1 : emu hc hρ μ (G (hf.toLp f)) (zextL hρ hW hWb φ) =
      inner ℝ (hf.toLp f) (zextL hρ hW hWb φ) := hG.eq _ hz
  have e2 : emu hc hρ μ (zextL hρ hW hWb v) (zextL hρ hW hWb φ) =
      ∫ x in W, ρ x * f x * φ.toH1Function.toFun x := by
    unfold emu
    rw [inner_zextL hρ hρpos hW hWb v φ, gradForm_zext hc hρ hcpos hρpos hW hWb v φ]
    exact hv φ
  rw [e1, e2, inner_toLp_zextL hρ hρpos hW hWb hf φ]
  ring

/-- **Céa's lemma** for the zero-extended variational solutions. -/
theorem cea_bound {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {μ : ℝ} (hμ : 0 < μ)
    {G : Lp ℝ 2 (wm ρ) →L[ℝ] Lp ℝ 2 (wm ρ)}
    (hG : DirichletForm.IsResolvent (gradClosedForm hc hρ hcpos hρpos) μ G)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) {f : St d → ℝ}
    (hf : MemLp f 2 (wm ρ)) (v : H10Function W)
    (hv : ∀ φ : H10Function W,
      μ * ∫ x in W, ρ x * v.toH1Function.toFun x * φ.toH1Function.toFun x ∂volume +
        ∫ x in W, vecDot (c x • v.toH1Function.grad x) (φ.toH1Function.grad x) ∂volume =
      ∫ x in W, ρ x * f x * φ.toH1Function.toFun x ∂volume)
    (w : H10Function W) :
    emu hc hρ μ (G (hf.toLp f) - zextL hρ hW hWb v) (G (hf.toLp f) - zextL hρ hW hWb v) ≤
      emu hc hρ μ (G (hf.toLp f) - zextL hρ hW hWb w) (G (hf.toLp f) - zextL hρ hW hWb w) := by
  set g := G (hf.toLp f) with hg
  have hgd : g ∈ gradDomain hc hρ := hG.mem_domain _
  have hzv := zextL_mem_gradDomain hc hρ hcpos hρpos hW hWb v
  have hzw := zextL_mem_gradDomain hc hρ hcpos hρpos hW hWb w
  have hzwv := zextL_mem_gradDomain hc hρ hcpos hρpos hW hWb (w - v)
  set e := g - zextL hρ hW hWb v with he
  set y := g - zextL hρ hW hWb w with hy
  set x := zextL hρ hW hWb (w - v) with hx
  have hed : e ∈ gradDomain hc hρ := (gradDomain hc hρ).sub_mem hgd hzv
  have hyd : y ∈ gradDomain hc hρ := (gradDomain hc hρ).sub_mem hgd hzw
  have hxe : e - x = y := by
    rw [hx, zextL_sub hρ hW hWb w v, he, hy]; abel
  have horth : emu hc hρ μ e x = 0 := galerkin_orthogonal hc hρ hcpos hρpos hG hW hWb hf v hv (w - v)
  have hey : emu hc hρ μ e y = emu hc hρ μ e e := by
    rw [emu_comm hc hρ hcpos hρpos μ hed hyd, ← hxe,
      emu_sub_left hc hρ hcpos hρpos μ hed hzwv hed, emu_comm hc hρ hcpos hρpos μ hzwv hed,
      horth, sub_zero]
  have hcs := emu_sq_le hc hρ hcpos hρpos hμ.le hed hyd
  have hee := emu_self_nonneg hc hρ hcpos hρpos hμ.le hed
  have hyy := emu_self_nonneg hc hρ hcpos hρpos hμ.le hyd
  rw [hey] at hcs
  by_contra hlt
  push_neg at hlt
  nlinarith [mul_pos (lt_of_le_of_lt hyy hlt) (lt_of_le_of_lt hyy hlt)]

/-- A test function supported in `W` is the zero extension of its `H¹₀(W)` restriction. -/
theorem zextL_ofContDiff {ρ : St d → ℝ} (hρ : Continuous ρ) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) {φ : St d → ℝ} (hφ : φ ∈ testFns d) (hsub : tsupport φ ⊆ W) :
    zextL hρ hW hWb (H10Function.ofContDiff hW hφ.1 hφ.2 hsub) = tcls hρ φ hφ := by
  apply Lp.ext
  have hz : ∀ᵐ x ∂(wm ρ), zextL hρ hW hWb (H10Function.ofContDiff hW hφ.1 hφ.2 hsub) x =
      (H10Function.ofContDiff hW hφ.1 hφ.2 hsub).zeroExtension x := MemLp.coeFn_toLp _
  filter_upwards [hz, MemLp.coeFn_toLp (memLp_wm_of_test hρ hφ)] with x hx1 hx2
  rw [hx1]
  simp only [tcls]
  rw [hx2]
  by_cases hxW : x ∈ W
  · rw [H10Function.zeroExtension_apply_of_mem _ hxW]
    rfl
  · rw [H10Function.zeroExtension_apply_of_not_mem _ hxW]
    exact (image_eq_zero_of_notMem_tsupport (fun h => hxW (hsub h))).symm

/-- **Galerkin convergence**: the zero-extended `H¹₀(W_n)` variational solutions on an exhausting
family converge in `L²(ρ)` to the resolvent of the form. -/
theorem galerkin_tendsto {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {μ : ℝ} (hμ : 0 < μ)
    {G : Lp ℝ 2 (wm ρ) →L[ℝ] Lp ℝ 2 (wm ρ)}
    (hG : DirichletForm.IsResolvent (gradClosedForm hc hρ hcpos hρpos) μ G) {f : St d → ℝ}
    (hf : MemLp f 2 (wm ρ)) {Wn : ℕ → Set (Vec d)} (hWo : ∀ n, IsOpen (Wn n))
    (hWb : ∀ n, Bornology.IsBounded (Wn n))
    (hexh : ∀ φ ∈ testFns d, ∃ n0, ∀ n ≥ n0, tsupport φ ⊆ Wn n)
    (v : ∀ n, H10Function (Wn n))
    (hv : ∀ n (φ : H10Function (Wn n)),
      μ * ∫ x in Wn n, ρ x * (v n).toH1Function.toFun x * φ.toH1Function.toFun x ∂volume +
        ∫ x in Wn n, vecDot (c x • (v n).toH1Function.grad x) (φ.toH1Function.grad x) ∂volume =
      ∫ x in Wn n, ρ x * f x * φ.toH1Function.toFun x ∂volume) :
    Tendsto (fun n => zextL hρ (hWo n) (hWb n) (v n)) atTop (𝓝 (G (hf.toLp f))) := by
  set g := G (hf.toLp f) with hg
  have hgd : g ∈ gradDomain hc hρ := hG.mem_domain _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := max μ 1 with hM
  have hMpos : 0 < M := lt_max_of_lt_left hμ
  -- a test function with small energy distance
  obtain ⟨φs, hφs, h1, h2⟩ := exists_test_sequence hc hρ hcpos hρpos hgd
  have hen : Tendsto (fun k => (gradClosedForm hc hρ hcpos hρpos).energyNormSq (g - tcls hρ (φs k) (hφs k)))
      atTop (𝓝 0) := by
    have hform : ∀ k, (gradClosedForm hc hρ hcpos hρpos).energyNormSq
        (g - tcls hρ (φs k) (hφs k)) =
        ∑ i, ‖gradOf hc hρ g i - gcls hc (φs k) (hφs k) i‖ ^ 2 +
          ‖g - tcls hρ (φs k) (hφs k)‖ ^ 2 := fun k =>
      energyNormSq_sub_test hc hρ hcpos hρpos hgd (hφs k)
    have hA : ∀ i, Tendsto (fun k => ‖gradOf hc hρ g i - gcls hc (φs k) (hφs k) i‖ ^ 2)
        atTop (𝓝 0) := by
      intro i
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 (h2 i)).pow 2)
      rw [zero_pow (by norm_num)] at this
      exact this.congr fun k => by rw [norm_sub_rev]
    have hB : Tendsto (fun k => ‖g - tcls hρ (φs k) (hφs k)‖ ^ 2) atTop (𝓝 0) := by
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 h1).pow 2)
      rw [zero_pow (by norm_num)] at this
      exact this.congr fun k => by rw [norm_sub_rev]
    have := (tendsto_finset_sum Finset.univ fun i _ => hA i).add hB
    simpa [hform] using this
  obtain ⟨k, hk⟩ := (hen.eventually
    (gt_mem_nhds (show (0:ℝ) < μ * (ε / 2) ^ 2 / M by positivity))).exists
  obtain ⟨n0, hn0⟩ := hexh (φs k) (hφs k)
  refine ⟨n0, fun n hn => ?_⟩
  set w := H10Function.ofContDiff (hWo n) (hφs k).1 (hφs k).2 (hn0 n hn) with hw
  have hzw := zextL_ofContDiff hρ (hWo n) (hWb n) (hφs k) (hn0 n hn)
  have hcea := cea_bound hc hρ hcpos hρpos hμ hG (hWo n) (hWb n) hf (v n) (hv n) w
  rw [hzw] at hcea
  have hle := emu_self_le_energyNormSq hc hρ hcpos hρpos hμ.le (g - tcls hρ (φs k) (hφs k))
  have hzvd := zextL_mem_gradDomain hc hρ hcpos hρpos (hWo n) (hWb n) (v n)
  have hnorm := norm_sq_le_emu hc hρ hcpos hρpos hμ
    ((gradDomain hc hρ).sub_mem hgd hzvd)
  have hlt : ‖g - zextL hρ (hWo n) (hWb n) (v n)‖ ^ 2 < (ε / 2) ^ 2 := by
    have h3 : μ * ‖g - zextL hρ (hWo n) (hWb n) (v n)‖ ^ 2 < μ * (ε / 2) ^ 2 := by
      have := mul_lt_mul_of_pos_left hk hMpos
      rw [mul_div_cancel₀ _ hMpos.ne'] at this
      linarith
    exact lt_of_mul_lt_mul_left h3 hμ.le
  have h4 : ‖g - zextL hρ (hWo n) (hWb n) (v n)‖ < ε / 2 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [norm_nonneg (g - zextL hρ (hWo n) (hWb n) (v n))]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
  linarith

end SubdiffusiveProcess.E7
