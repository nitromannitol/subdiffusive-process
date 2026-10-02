import SubdiffusiveProcess.DirichletForm.FOTEnergyFamily
import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusChain
import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusCross
import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusLeibniz

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

theorem EnergyFamily.core_chain {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) {uc : X → ℝ}
    (huc : Continuous uc) (huae : ⇑u =ᵐ[m] uc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain) (hwae : ⇑w =ᵐ[m] fun x => Φ (uc x))
    {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal = ∫ x in B, (deriv Φ (uc x)) ^ 2 ∂(Γ.measure u) := by
  exact Γ.core_chain_formula h hu huc huae Φ hΦ hΦ0 hw hwae hB

theorem EnergyFamily.core_cross_chain {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) (hv : F.toClosedForm.MemCoreOn U v)
    {uc vc : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc)
    (Φ Ψ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) (hΨ : ContDiff ℝ 1 Ψ)
    (hΦ0 : Φ 0 = 0) (hΨ0 : Ψ 0 = 0)
    {w z : Lp ℝ 2 m} (hw : w ∈ F.domain) (hz : z ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (uc x)) (hzae : ⇑z =ᵐ[m] fun x => Ψ (vc x))
    {B : Set X} (hB : MeasurableSet B) :
    Γ.cross w z B = signedIntegralOn (Γ.cross u v) B
      (fun x => deriv Φ (uc x) * deriv Ψ (vc x)) := by
  exact Γ.core_cross_chain_formula h hu hv huc hvc huae hvae Φ Ψ hΦ hΨ hΦ0 hΨ0
    hw hz hwae hzae hB

theorem EnergyFamily.core_leibniz {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) (hv : F.toClosedForm.MemCoreOn U v)
    {uc vc : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => vc x * Φ (uc x)) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal =
      (∫ x in B, vc x ^ 2 * deriv Φ (uc x) ^ 2 ∂(Γ.measure u)) +
        2 * signedIntegralOn (Γ.cross u v) B
          (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) +
        (∫ x in B, Φ (uc x) ^ 2 ∂(Γ.measure v)) := by
  exact Γ.core_leibniz_formula h hu hv huc hvc huae hvae Φ hΦ hw hwae hB

theorem exists_bounded_energy_approx (F : _root_.DirichletForm m) {U : Set X}
    (h : Data F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {R : ℝ≥0}
    (huR : ∀ᵐ x ∂m, |u x| ≤ R) :
    ∃ (un : ℕ → Lp ℝ 2 m) (f : ℕ → X → ℝ),
      (∀ n, F.toClosedForm.MemCoreOn U (un n)) ∧
      (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U ∧
        ⇑(un n) =ᵐ[m] f n ∧ ∀ x, |f n x| ≤ R) ∧
      Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0) := by
  obtain ⟨C, hcore⟩ := h.core
  choose v hvC hvε using fun n : ℕ =>
    hcore.denseEnergy u hu (1 / ((n : ℝ) + 1)) (by positivity)
  have hv : ∀ n, F.toClosedForm.MemCoreOn U (v n) :=
    fun n => hcore.memCoreOn _ (hvC n)
  choose f hf hfc hfU hfae using fun n => (hv n).2
  have he : Tendsto (fun n => F.energyNormSq (v n - u)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => F.toClosedForm.energyNormSq_nonneg (F.domain.sub_mem (hv n).1 hu))
      _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [F.toClosedForm.energyNormSq_sub_comm (hv n).1 hu]
    exact (hvε n).le
  have hL2 : Tendsto v atTop (𝓝 u) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs : Tendsto (fun n => ‖v n - u‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _) (fun n =>
        F.toClosedForm.sq_norm_le_energyNormSq (F.domain.sub_mem (hv n).1 hu)) he
    have ht : Tendsto (fun n => Real.sqrt (‖v n - u‖ ^ 2)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hs
    exact ht.congr fun n => Real.sqrt_sq (norm_nonneg _)
  have hcross := F.toClosedForm.tendsto_form_of_tendsto_energyNormSq
    (fun n => (hv n).1) hu hu he
  have hdiff : Tendsto (fun n => F.form (v n - u) (v n - u)) atTop (𝓝 0) :=
    squeeze_zero (fun n => F.form_nonneg _ (F.domain.sub_mem (hv n).1 hu))
      (fun n => F.toClosedForm.form_le_energyNormSq) he
  have henergy : Tendsto (fun n => F.form (v n) (v n)) atTop (𝓝 (F.form u u)) := by
    have ht := hdiff.add ((hcross.sub_const (F.form u u)).const_mul 2)
    have ht' := ht.add_const (F.form u u)
    simp only [sub_self, mul_zero, zero_add] at ht'
    apply ht'.congr
    intro n
    rw [F.toClosedForm.form_sub_self (hv n).1 hu]
    ring
  refine ⟨fun n => clipLp R (v n), fun n => clip R ∘ f n,
    fun n => memCoreOn_compLp F (hv n) (lipschitzWith_clip R) (clip_zero R.coe_nonneg),
    fun n => ⟨(lipschitzWith_clip R).continuous.comp (hf n),
      (hfc n).comp_left (clip_zero R.coe_nonneg),
      (tsupport_comp_subset (clip_zero R.coe_nonneg) (f n)).trans (hfU n),
      (coeFn_clipLp R (v n)).trans ((hfae n).fun_comp (clip R)),
      fun x => abs_clip_le R.coe_nonneg (f n x)⟩, ?_⟩
  have hc := ((lipschitzWith_clip R).continuous_compLp
    (μ := m) (p := 2) (clip_zero R.coe_nonneg)).tendsto u |>.comp hL2
  change Tendsto (fun n => clipLp R (v n)) atTop (𝓝 (clipLp R u)) at hc
  rw [clipLp_eq_self huR] at hc
  apply energy_tendsto_of_limsup_le F.toClosedForm
    (fun n => (clipLp_mem F R (hv n).1).1) hu hc
  intro ε hε
  filter_upwards [henergy.eventually (gt_mem_nhds (by linarith : F.form u u < F.form u u + ε))]
    with n hn
  exact (clipLp_mem F R (hv n).1).2.trans hn.le

end DirichletForm.FOTConstruction
