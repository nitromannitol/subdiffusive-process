import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblyLocalization
import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblyIntegration
import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblyLeibniz

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] {m : Measure X}

theorem EnergyFamily.continuous_chain {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {uc : X → ℝ}
    (huc : Continuous uc) (huae : ⇑u =ᵐ[m] uc) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0) {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (uc x)) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal = ∫ x in B, (deriv Φ (uc x)) ^ 2 ∂(Γ.measure u) := by
  have hden : Γ.measure w = (Γ.measure u).withDensity
      (fun x => ENNReal.ofReal ((deriv Φ (uc x)) ^ 2)) := by
    let O : ℕ → Set X := fun n => {x | |uc x| < (n : ℝ) + 1}
    have hO : ∀ n, IsOpen (O n) := fun n =>
      isOpen_lt huc.abs continuous_const
    have hcover : ⋃ n, O n = univ := by
      apply iUnion_eq_univ_iff.mpr
      intro x
      obtain ⟨n, hn⟩ := exists_nat_gt |uc x|
      exact ⟨n, by change |uc x| < (n : ℝ) + 1; linarith⟩
    apply Measure.ext_of_iUnion_eq_univ hcover
    intro n
    obtain ⟨Ψ, hΨ, hΨ0, ⟨L, hL⟩, hΨeq⟩ :=
      assembly_c1_modification Φ hΦ hΦ0 ((n : ℝ) + 1) (by positivity)
    let z : Lp ℝ 2 m := hL.compLp hΨ0 u
    have hzrep : ⇑z =ᵐ[m] fun x => Ψ (uc x) := by
      filter_upwards [LipschitzWith.coeFn_compLp hL hΨ0 u, huae] with x hx hu'
      rw [hx]
      change Ψ (u x) = Ψ (uc x)
      rw [hu']
    have hz : z ∈ F.domain := (lipschitz_comp_mem F hL hΨ0 hu
      (LipschitzWith.coeFn_compLp hL hΨ0 u)).1
    have heq : ⇑w =ᵐ[m.restrict (O n)] ⇑z := by
      filter_upwards [ae_restrict_of_ae hwae, ae_restrict_of_ae hzrep,
        ae_restrict_mem (hO n).measurableSet] with x hw' hz' hx
      rw [hw', hz']
      exact ((hΨeq (uc x) hx).self_of_nhds).symm
    rw [Γ.locality h hw hz (hO n) heq,
      Γ.continuous_lipschitz_density h q hu huc huae Ψ hΨ hL hΨ0 hz hzrep,
      restrict_withDensity (hO n).measurableSet,
      restrict_withDensity (hO n).measurableSet]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (hO n).measurableSet] with x hx
    rw [(hΨeq (uc x) hx).deriv_eq]
  rw [hden, withDensity_apply _ hB]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => sq_nonneg _)
    (((hΦ.continuous_deriv (by norm_num)).comp huc).pow 2).measurable.aestronglyMeasurable).symm

theorem EnergyFamily.continuous_leibniz {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCore u) (hv : F.toClosedForm.MemCore v)
    {uc vc : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ 1 Φ) {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => vc x * Φ (uc x)) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal =
      (∫ x in B, vc x ^ 2 * deriv Φ (uc x) ^ 2 ∂(Γ.measure u)) +
        2 * signedIntegralOn (Γ.cross u v) B
          (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) +
        (∫ x in B, Φ (uc x) ^ 2 ∂(Γ.measure v)) := by
  obtain ⟨f, hf, hfc, _, hfae⟩ := hu.hasCoreRep
  obtain ⟨g, hg, hgc, _, hgae⟩ := hv.hasCoreRep
  have huc_eq : ∀ z ∈ F.domain, uc =ᵐ[Γ.measure z] f := fun z hz =>
    (q.continuous_agree u hu.1 uc huc huae z hz).symm.trans
      (q.continuous_agree u hu.1 f hf hfae z hz)
  have hvc_eq : ∀ z ∈ F.domain, vc =ᵐ[Γ.measure z] g := fun z hz =>
    (q.continuous_agree v hv.1 vc hvc hvae z hz).symm.trans
      (q.continuous_agree v hv.1 g hg hgae z hz)
  have hprod : ⇑w =ᵐ[m] fun x => g x * Φ (f x) := by
    filter_upwards [hwae, huae, hvae, hfae, hgae] with x hx h1 h2 h3 h4
    rw [hx, ← h1, ← h2, h3, h4]
  have hI1 : (∫ x in B, vc x ^ 2 * deriv Φ (uc x) ^ 2 ∂Γ.measure u) =
      ∫ x in B, g x ^ 2 * deriv Φ (f x) ^ 2 ∂Γ.measure u := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (huc_eq u hu.1),
      ae_restrict_of_ae (hvc_eq u hu.1)] with x hx hy
    rw [hx, hy]
  have hI3 : (∫ x in B, Φ (uc x) ^ 2 ∂Γ.measure v) =
      ∫ x in B, Φ (f x) ^ 2 ∂Γ.measure v := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (huc_eq v hv.1)] with x hx
    rw [hx]
  have hcrossU := (SignedMeasure.totalVariation_absolutelyContinuous_iff _ _).mp
    (Γ.cross_absolutelyContinuous_left hu.1 hv.1)
  have hcrossV : (Γ.cross u v).toJordanDecomposition.posPart ≪ Γ.measure v ∧
      (Γ.cross u v).toJordanDecomposition.negPart ≪ Γ.measure v := by
    rw [Γ.cross_symm u hu.1 v hv.1]
    exact (SignedMeasure.totalVariation_absolutelyContinuous_iff _ _).mp
      (Γ.cross_absolutelyContinuous_left hv.1 hu.1)
  have hI2 : signedIntegralOn (Γ.cross u v) B
      (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) =
        signedIntegralOn (Γ.cross u v) B (fun x => g x * Φ (f x) * deriv Φ (f x)) := by
    simp only [signedIntegralOn]
    congr 1
    · apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (hcrossU.1.ae_eq (huc_eq u hu.1)),
        ae_restrict_of_ae (hcrossV.1.ae_eq (hvc_eq v hv.1))] with x hx hy
      rw [hx, hy]
    · apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (hcrossU.2.ae_eq (huc_eq u hu.1)),
        ae_restrict_of_ae (hcrossV.2.ae_eq (hvc_eq v hv.1))] with x hx hy
      rw [hx, hy]
  rw [hI1, hI2, hI3]
  exact Γ.leibniz_compact h hu hv hf hg hfc hgc hfae hgae Φ hΦ hw hprod hB

theorem EnergyFamily.continuous_defining {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u φ : Lp ℝ 2 m} (hu : F.toClosedForm.MemCore u) (hφ : F.toClosedForm.MemCore φ)
    {uc φc : X → ℝ} (huc : Continuous uc) (hφc : Continuous φc)
    (huae : ⇑u =ᵐ[m] uc) (hφae : ⇑φ =ᵐ[m] φc)
    {uφ u2 : Lp ℝ 2 m} (huφ : uφ ∈ F.domain) (hu2 : u2 ∈ F.domain)
    (hprod : ⇑uφ =ᵐ[m] fun x => uc x * φc x) (hsq : ⇑u2 =ᵐ[m] fun x => uc x ^ 2) :
    (∫ x, φc x ∂(Γ.measure u)) = F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ := by
  obtain ⟨f, hf, hfc, _, hfae⟩ := hu.hasCoreRep
  obtain ⟨g, hg, hgc, _, hgae⟩ := hφ.hasCoreRep
  obtain ⟨Cf, hCf⟩ := hfc.exists_bound_of_continuous hf
  obtain ⟨Cg, hCg⟩ := hgc.exists_bound_of_continuous hg
  let R : ℝ≥0 := ⟨max 0 (max Cf Cg), le_max_left _ _⟩
  have hfR : ∀ x, |f x| ≤ R := fun x =>
    (hCf x).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hgR : ∀ x, |g x| ≤ R := fun x =>
    (hCg x).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hprod' : ⇑uφ =ᵐ[m] fun x => f x * g x := by
    filter_upwards [hprod, huae, hφae, hfae, hgae] with x hx h1 h2 h3 h4
    rw [hx, ← h1, ← h2, h3, h4]
  have hsq' : ⇑u2 =ᵐ[m] fun x => f x ^ 2 := by
    filter_upwards [hsq, huae, hfae] with x hx h1 h2
    rw [hx, ← h1, h2]
  calc
    _ = ∫ x, g x ∂Γ.measure u := integral_congr_ae
      ((q.continuous_agree φ hφ.1 φc hφc hφae u hu.1).symm.trans
        (q.continuous_agree φ hφ.1 g hg hgae u hu.1))
    _ = _ := Γ.defining_bounded h q hu.1 hφ.1 hf hg hfae hgae R hfR hgR
      huφ hu2 hprod' hsq' 

theorem EnergyFamily.continuous_support {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    {f : X → ℝ} (hf : Continuous f) (hae : ⇑u =ᵐ[m] f) :
    Γ.measure u (tsupport f)ᶜ = 0 := by
  have hzD : (0 : Lp ℝ 2 m) ∈ F.domain := F.domain.zero_mem
  have hz : Γ.measure (0 : Lp ℝ 2 m) univ = 0 := by
    have hmass : (Γ.measure (0 : Lp ℝ 2 m) univ).toReal = 0 := by
      rw [Γ.mass 0 hzD, F.form_zero_left hzD]
    exact (ENNReal.toReal_eq_zero_iff _).1 hmass |>.resolve_right (Γ.finite 0 hzD).ne
  have hO : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  have heq : ⇑u =ᵐ[m.restrict (tsupport f)ᶜ] ⇑(0 : Lp ℝ 2 m) := by
    filter_upwards [ae_restrict_of_ae hae,
      ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 m),
      ae_restrict_mem hO.measurableSet] with x hx hz hxO
    rw [hx, hz]
    exact image_eq_zero_of_notMem_tsupport hxO
  have hres := Γ.locality h hu hzD hO heq
  have hmass := congrArg (fun μ : Measure X => μ univ) hres
  simpa only [Measure.restrict_apply_univ,
    measure_mono_null (subset_univ _) hz] using hmass

theorem EnergyFamily.exists_energyMeasure {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ) :
    ∃ G : EnergyMeasure F.toClosedForm,
      (∀ u ∈ F.domain, G.measure u = Γ.measure u) ∧
      (∀ u ∈ F.domain, ∀ v ∈ F.domain, G.cross u v = Γ.cross u v) := by
  let G : EnergyMeasure F.toClosedForm :=
    { measure := Γ.measure
      cross := Γ.cross
      measure_univ_lt_top := Γ.finite
      measure_univ := Γ.mass
      cross_symm := Γ.cross_symm
      cross_self := Γ.cross_self
      cross_add_right := Γ.cross_add_right
      cross_smul_right := Γ.cross_smul_right
      cross_univ := Γ.cross_univ
      abs_cross_le := Γ.cross_le
      locality := fun _ hu _ hw _ hO heq => Γ.locality h hu hw hO heq
      regular := Γ.regular
      measure_compl_tsupport := fun _ hu _ hf hae => Γ.continuous_support h hu hf hae
      chain_rule := fun _ hu _ huc huae Φ hΦ hΦ0 _ hw hwae _ hB =>
        Γ.continuous_chain h q hu huc huae Φ hΦ hΦ0 hw hwae hB
      leibniz := fun _ _ hu hv _ _ huc hvc huae hvae Φ hΦ _ hw hwae _ hB =>
        Γ.continuous_leibniz h q hu hv huc hvc huae hvae Φ hΦ hw hwae hB
      defining_identity := fun _ _ hu hφ _ _ huc hφc huae hφae _ _ huφ hu2 hprod hsq =>
        Γ.continuous_defining h q hu hφ huc hφc huae hφae huφ hu2 hprod hsq }
  exact ⟨G, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

end DirichletForm.FOTConstruction
