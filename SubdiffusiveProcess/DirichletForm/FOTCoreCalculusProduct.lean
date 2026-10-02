import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusCross
import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusDensity

open MeasureTheory Filter Set Topology
open scoped ContDiff

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}
  {F : _root_.DirichletForm m} {U : Set X}

theorem EnergyFamily.core_density_integrable (h : Data F U) (Γ : EnergyFamily F U)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u) (hv : v ∈ F.domain)
    (k : X → ℝ) {f : X → ℝ} (hf : Continuous f) :
    SignedIntegrable (signedDensity (Γ.cross u v) k) f := by
  obtain ⟨g, hg, hgc, hgU, hgae⟩ := hu.2
  exact signedDensity_integrable _ hgc
    ((Γ.cross_variation_ac_left hu.1 hv) (Γ.measure_compl_tsupport h hu.1 hgae)) k hf

theorem EnergyFamily.core_density_integral (h : Data F U) (Γ : EnergyFamily F U)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u) (hv : v ∈ F.domain)
    {k f : X → ℝ} (hk : Continuous k) (hf : Continuous f) {B : Set X} (hB : MeasurableSet B) :
    _root_.DirichletForm.signedIntegralOn (signedDensity (Γ.cross u v) k) B f =
      _root_.DirichletForm.signedIntegralOn (Γ.cross u v) B (fun x => k x * f x) := by
  obtain ⟨g, hg, hgc, hgU, hgae⟩ := hu.2
  exact signedDensity_integral _ hgc
    ((Γ.cross_variation_ac_left hu.1 hv) (Γ.measure_compl_tsupport h hu.1 hgae)) hk hf hB

/-- Polarization of the square chain rule gives the cross product rule. -/
theorem EnergyFamily.core_cross_product_measure (h : Data F U) (Γ : EnergyFamily F U)
    {u v z : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : F.toClosedForm.MemCoreOn U v) (hz : F.toClosedForm.MemCoreOn U z)
    {uc vc zc : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc) (hzc : Continuous zc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc) (hzae : ⇑z =ᵐ[m] zc)
    {p : Lp ℝ 2 m} (hp : p ∈ F.domain) (hpae : ⇑p =ᵐ[m] fun x => uc x * vc x) :
    Γ.cross p z = signedDensity (Γ.cross u z) vc + signedDensity (Γ.cross v z) uc := by
  let S : ℝ → ℝ := fun t => t ^ 2
  have hS : ContDiff ℝ 1 S := contDiff_id.pow 2
  have hS0 : S 0 = 0 := by norm_num [S]
  have hder : ∀ t : ℝ, deriv S t = 2 * t := by
    intro t
    simpa [S] using ((hasDerivAt_id t).pow 2).deriv
  have hs := hu.add hv
  have hsae : ⇑(u + v) =ᵐ[m] fun x => uc x + vc x := by
    filter_upwards [Lp.coeFn_add u v, huae, hvae] with x hx hx1 hx2
    simp only [hx, Pi.add_apply, hx1, hx2]
  obtain ⟨a, ha, haae⟩ := F.comp_mem (u + v) hs.memCore S hS hS0
  obtain ⟨b, hb, hbae⟩ := F.comp_mem u hu.memCore S hS hS0
  obtain ⟨c, hc, hcae⟩ := F.comp_mem v hv.memCore S hS hS0
  have haar : ⇑a =ᵐ[m] fun x => S (uc x + vc x) := haae.trans (hsae.fun_comp S)
  have hbar : ⇑b =ᵐ[m] fun x => S (uc x) := hbae.trans (huae.fun_comp S)
  have hcar : ⇑c =ᵐ[m] fun x => S (vc x) := hcae.trans (hvae.fun_comp S)
  have heq : p = (1 / 2 : ℝ) • (a + (-1 : ℝ) • b + (-1 : ℝ) • c) := by
    apply Lp.ext
    filter_upwards [hpae, Lp.coeFn_smul (1 / 2 : ℝ) (a + (-1 : ℝ) • b + (-1 : ℝ) • c),
      Lp.coeFn_add (a + (-1 : ℝ) • b) ((-1 : ℝ) • c), Lp.coeFn_add a ((-1 : ℝ) • b),
      Lp.coeFn_smul (-1 : ℝ) b, Lp.coeFn_smul (-1 : ℝ) c, haar, hbar, hcar]
      with x e0 e1 e2 e3 e4 e5 e6 e7 e8
    simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, S]
    ring
  ext B hB
  have hchain (r : Lp ℝ 2 m) (hr : F.toClosedForm.MemCoreOn U r)
      (rc : X → ℝ) (hrc : Continuous rc) (hrae : ⇑r =ᵐ[m] rc)
      (q : Lp ℝ 2 m) (hq : q ∈ F.domain) (hqae : ⇑q =ᵐ[m] fun x => S (rc x)) :
      Γ.cross q z B = 2 * _root_.DirichletForm.signedIntegralOn (Γ.cross r z) B rc := by
    have ht := Γ.core_cross_chain_formula h hr hz hrc hzc hrae hzae S id hS contDiff_id
      hS0 rfl hq hz.1 hqae (by simpa only [id_eq] using hzae) hB
    simp only [hder, deriv_id, mul_one] at ht
    rw [ht, signedIntegralOn_const_mul]
  have hA := hchain (u + v) hs _ (huc.add hvc) hsae a ha.1 haar
  have hC := hchain u hu uc huc huae b hb.1 hbar
  have hD := hchain v hv vc hvc hvae c hc.1 hcar
  rw [Γ.signedIntegralOn_cross_add_left h hu hv hz.1 (huc.add hvc) B,
    signedIntegralOn_add _ (Γ.core_signedIntegrable h hu hz.1 huc)
      (Γ.core_signedIntegrable h hu hz.1 hvc),
    signedIntegralOn_add _ (Γ.core_signedIntegrable h hv hz.1 huc)
      (Γ.core_signedIntegrable h hv hz.1 hvc)] at hA
  rw [heq, Γ.cross_smul_left (1 / 2 : ℝ)
    (F.domain.add_mem (F.domain.add_mem ha.1 (F.domain.smul_mem (-1) hb.1))
      (F.domain.smul_mem (-1) hc.1)) hz.1,
    Γ.cross_add_left (F.domain.add_mem ha.1 (F.domain.smul_mem (-1) hb.1))
      (F.domain.smul_mem (-1) hc.1) hz.1,
    Γ.cross_add_left ha.1 (F.domain.smul_mem (-1) hb.1) hz.1,
    Γ.cross_smul_left (-1) hb.1 hz.1, Γ.cross_smul_left (-1) hc.1 hz.1,
    VectorMeasure.smul_apply, VectorMeasure.add_apply, VectorMeasure.add_apply,
    VectorMeasure.smul_apply, VectorMeasure.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    VectorMeasure.add_apply,
    signedDensity_apply _ (Γ.core_signedIntegrable h hu hz.1 hvc) hB,
    signedDensity_apply _ (Γ.core_signedIntegrable h hv hz.1 huc) hB]
  linarith only [hA, hC, hD]

theorem core_mul_composition {u v : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) (hv : F.toClosedForm.MemCoreOn U v)
    {uc vc : X → ℝ} (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {w : Lp ℝ 2 m}
    (hwae : ⇑w =ᵐ[m] fun x => vc x * Φ (uc x)) : F.toClosedForm.MemCoreOn U w := by
  obtain ⟨p, hp, hpae⟩ := F.exists_memCoreOn_mul_comp U hu.memCore hv huae hvae hΦ
  have heq : w = p := Lp.ext (hwae.trans hpae.symm)
  rwa [heq]

theorem EnergyFamily.core_cross_mul_comp_measure (h : Data F U) (Γ : EnergyFamily F U)
    {u v z : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : F.toClosedForm.MemCoreOn U v) (hz : F.toClosedForm.MemCoreOn U z)
    {uc vc zc : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc) (hzc : Continuous zc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc) (hzae : ⇑z =ᵐ[m] zc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) {w : Lp ℝ 2 m}
    (hwae : ⇑w =ᵐ[m] fun x => vc x * Φ (uc x)) :
    Γ.cross w z = signedDensity (Γ.cross u z) (fun x => vc x * deriv Φ (uc x)) +
      signedDensity (Γ.cross v z) (fun x => Φ (uc x)) := by
  let T : ℝ → ℝ := fun t => Φ t - Φ 0
  have hT : ContDiff ℝ 1 T := hΦ.sub contDiff_const
  have hT0 : T 0 = 0 := sub_self _
  have hder : deriv T = deriv Φ := by
    funext t
    exact ((hΦ.differentiable le_rfl t).hasDerivAt.sub_const (Φ 0)).deriv
  obtain ⟨a, ha, haae⟩ := F.comp_mem u hu.memCore T hT hT0
  have haar : ⇑a =ᵐ[m] fun x => T (uc x) := haae.trans (huae.fun_comp T)
  have haU := core_composition hu huae hT.continuous hT0 ha.1 haar
  have hac : Continuous (fun x => T (uc x)) := hT.continuous.comp huc
  obtain ⟨p, hp, hpae⟩ := F.exists_memCoreOn_mul_comp U haU.memCore hv haar hvae
    (Φ := id) contDiff_id
  have hpar : ⇑p =ᵐ[m] fun x => T (uc x) * vc x := by
    filter_upwards [hpae] with x hx
    simpa only [id_eq, mul_comm] using hx
  have heq : w = p + Φ 0 • v := by
    apply Lp.ext
    filter_upwards [hwae, hpae, Lp.coeFn_add p (Φ 0 • v), Lp.coeFn_smul (Φ 0) v, hvae]
      with x e0 e1 e2 e3 e4
    simp only [e0, e2, Pi.add_apply, e1, e3, Pi.smul_apply, smul_eq_mul, e4, id_eq, T]
    ring
  have hchain : Γ.cross a z = signedDensity (Γ.cross u z) (fun x => deriv Φ (uc x)) := by
    ext B hB
    rw [signedDensity_apply _ (Γ.core_signedIntegrable h hu hz.1
      (show Continuous (fun x => deriv Φ (uc x)) from
        (hΦ.continuous_deriv le_rfl).comp huc)) hB]
    have ht := Γ.core_cross_chain_formula h hu hz huc hzc huae hzae T id hT contDiff_id
      hT0 rfl ha.1 hz.1 haar (by simpa only [id_eq] using hzae) hB
    simpa only [hder, deriv_id, mul_one] using ht
  have hprod := Γ.core_cross_product_measure h haU hv hz hac hvc hzc haar hvae hzae hp.1 hpar
  rw [heq, Γ.cross_add_left hp.1 (F.domain.smul_mem (Φ 0) hv.1) hz.1,
    Γ.cross_smul_left (Φ 0) hv.1 hz.1, hprod, hchain]
  obtain ⟨fu, hfu, hfuc, hfuU, hfuae⟩ := hu.2
  obtain ⟨fv, hfv, hfvc, hfvU, hfvae⟩ := hv.2
  have hνu := (Γ.cross_variation_ac_left hu.1 hz.1)
    (Γ.measure_compl_tsupport h hu.1 hfuae)
  have hνv := (Γ.cross_variation_ac_left hv.1 hz.1)
    (Γ.measure_compl_tsupport h hv.1 hfvae)
  rw [signedDensity_mul _ hfuc hνu (show Continuous (fun x => deriv Φ (uc x)) from
    (hΦ.continuous_deriv le_rfl).comp huc) hvc]
  have hcomm : (fun x => deriv Φ (uc x) * vc x) = (fun x => vc x * deriv Φ (uc x)) := by
    funext x; ring
  rw [hcomm, add_assoc, ← signedDensity_add_const _ hfvc hνv hac (Φ 0)]
  congr 2
  funext x
  dsimp [T]
  ring

theorem EnergyFamily.core_cross_mul_comp_integral (h : Data F U) (Γ : EnergyFamily F U)
    {u v z : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : F.toClosedForm.MemCoreOn U v) (hz : F.toClosedForm.MemCoreOn U z)
    {uc vc zc : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc) (hzc : Continuous zc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc) (hzae : ⇑z =ᵐ[m] zc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) {w : Lp ℝ 2 m}
    (hwae : ⇑w =ᵐ[m] fun x => vc x * Φ (uc x))
    {f : X → ℝ} (hf : Continuous f) {B : Set X} (hB : MeasurableSet B) :
    _root_.DirichletForm.signedIntegralOn (Γ.cross w z) B f =
      _root_.DirichletForm.signedIntegralOn (Γ.cross u z) B
        (fun x => vc x * deriv Φ (uc x) * f x) +
      _root_.DirichletForm.signedIntegralOn (Γ.cross v z) B
        (fun x => Φ (uc x) * f x) := by
  have heq := Γ.core_cross_mul_comp_measure h hu hv hz huc hvc hzc huae hvae hzae Φ hΦ hwae
  have hw := core_mul_composition hu hv huae hvae hΦ hwae
  have hi := Γ.core_signedIntegrable h hw hz.1 hf
  rw [heq] at hi ⊢
  rw [signedIntegralOn_add_measure (Γ.core_density_integrable h hu hz.1 _ hf)
      (Γ.core_density_integrable h hv hz.1 _ hf) hi,
    Γ.core_density_integral h hu hz.1 (show Continuous (fun x => vc x * deriv Φ (uc x)) from
      hvc.mul ((hΦ.continuous_deriv le_rfl).comp huc)) hf hB,
    Γ.core_density_integral h hv hz.1 (show Continuous (fun x => Φ (uc x)) from
      hΦ.continuous.comp huc) hf hB]

end DirichletForm.FOTConstruction
