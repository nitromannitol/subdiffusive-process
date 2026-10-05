module

public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_endpoints_support_2
public import SubdiffusiveProcess.Paper.lem_endpoints_support_3
public import SubdiffusiveProcess.Paper.lem_endpoints_support_4
public import SubdiffusiveProcess.Paper.lem_endpoints_support_6
public import SubdiffusiveProcess.Paper.prop_21_catalog_global_weighted_energy

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess.Paper

theorem aux_lem_endpoints_support_7_coefficient_weight_lower
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (a b : PositiveCoefficient Q)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x)
    (q : Set (SpatialCoordinates d)) (K : ℝ) (hK : 0 < K)
    (hlow : ∀ x ∈ q, K ≤ rho x) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → a.val x ≤ K⁻¹ * b.val x := by
  filter_upwards [hweight, aux_prop_locality_recovery_coeff_nonneg a] with x hx hax hxq
  apply (le_inv_mul_iff₀ hK).mpr
  rw [hx]
  exact mul_le_mul_of_nonneg_right (hlow x hxq) hax

section Weight
variable {d : ℕ} {hd : 2 ≤ d} {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
  {H : BilateralField d → C(SpatialCoordinates d, ℝ)} {om om' : BilateralField d}
  {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
  {S : ResponseSpace (centeredCube z r hr)}
  {G G' : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
  {N N1 N2 : ℕ → ℕ}

theorem aux_lem_endpoints_support_7_side_global_form_le
    (A : aux_lem_endpoints_support_6_limit_side d hd model H om z r hr S G N1)
    (B : aux_lem_endpoints_support_6_limit_side d hd model H om' z r hr S G' N2)
    (RA : aux_lem_endpoints_support_6_resp_side d model H om z r hr S G N)
    (RB : aux_lem_endpoints_support_6_resp_side d model H om' z r hr S G' N)
    (K : ℝ)
    (hcoeff : ∀ᶠ n in atTop,
      ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N n) z hr).val x ≤
        K * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr).val x) :
    ∀ u ∈ A.form.domain, u ∈ B.form.domain ∧ B.form.form u u ≤ K * A.form.form u u := by
  have hA := aux_in_represented_mosco_free d hd model H om z r hr S G N RA.response
    RA.response_eq RA.response_tendsto
  have hB := aux_in_represented_mosco_free d hd model H om' z r hr S G' N RB.response
    RB.response_eq RB.response_tendsto
  have hpass := aux_lem_endpoints_support_6_global_energy_order S
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr)
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N n) z hr)
    G G' hA.2.2 hB.2.1 K hcoeff
  intro u hu
  have huG : u ∈ limitFormDomain G :=
    aux_lem_endpoints_support_6_domain_eq_of_energy A.form.toClosedForm G A.energy_eq ▸ hu
  obtain ⟨huG', hle⟩ := hpass u huG
  have huB : u ∈ B.form.domain :=
    aux_lem_endpoints_support_6_domain_mem_of_energy B.form.toClosedForm G' B.energy_eq huG'
  rw [← aux_lem_endpoints_support_6_form_eq_toReal_energy A.form.toClosedForm G A.energy_eq u hu,
    ← aux_lem_endpoints_support_6_form_eq_toReal_energy B.form.toClosedForm G' B.energy_eq u huB] at hle
  exact ⟨huB, hle⟩

theorem aux_lem_endpoints_support_7_side_weight_domain
    (A : aux_lem_endpoints_support_6_limit_side d hd model H om z r hr S G N1)
    (B : aux_lem_endpoints_support_6_limit_side d hd model H om' z r hr S G' N2)
    (RA : aux_lem_endpoints_support_6_resp_side d model H om z r hr S G N2)
    (RB : aux_lem_endpoints_support_6_resp_side d model H om' z r hr S G' N1)
    (rho : C(SpatialCoordinates d, ℝ)) (hpos : ∀ x, 0 < rho x)
    (hweight1 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N1 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N1 n) z hr).val x)
    (hweight2 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N2 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N2 n) z hr).val x) :
    A.form.domain = B.form.domain := by
  obtain ⟨lo, hi, hlo, _hhi, hb⟩ := aux_lem_endpoints_support_6_weight_compact_bounds z r hr rho hpos
  have hforward := aux_lem_endpoints_support_7_side_global_form_le A B A.resp RB hi (by
    filter_upwards [hweight1] with n hn
    have hh := lem_endpoints_support_6 _ _ rho hn
      (centeredCube z r hr : Set (SpatialCoordinates d)) hi
      (fun x hx => (hb x (subset_closure hx)).2)
    filter_upwards [hh, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxQ
    exact hx hxQ)
  have hreverse := aux_lem_endpoints_support_7_side_global_form_le B A B.resp RA lo⁻¹ (by
    filter_upwards [hweight2] with n hn
    have hh := aux_lem_endpoints_support_7_coefficient_weight_lower _ _ rho hn
      (centeredCube z r hr : Set (SpatialCoordinates d)) lo hlo
      (fun x hx => (hb x (subset_closure hx)).1)
    filter_upwards [hh, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxQ
    exact hx hxQ)
  exact le_antisymm (fun u hu => (hforward u hu).1) (fun u hu => (hreverse u hu).1)

theorem aux_lem_endpoints_support_7_side_weight_local_bounds
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (A : aux_lem_endpoints_support_6_limit_side d hd model H om z r hr S G N1)
    (B : aux_lem_endpoints_support_6_limit_side d hd model H om' z r hr S G' N2)
    (RA : aux_lem_endpoints_support_6_resp_side d model H om z r hr S G N2)
    (RB : aux_lem_endpoints_support_6_resp_side d model H om' z r hr S G' N1)
    (rho : C(SpatialCoordinates d, ℝ))
    (hdom : A.form.domain = B.form.domain)
    (hweight1 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N1 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N1 n) z hr).val x)
    (hweight2 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N2 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N2 n) z hr).val x)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hb : ∀ x ∈ q, lo ≤ rho x ∧ rho x ≤ hi)
    (u : DomainL2 (centeredCube z r hr)) (hu : A.form.toClosedForm.MemCore u)
    (T : Set (SpatialCoordinates d)) (hTq : T ⊆ q) :
    lo * (A.gamma.measure u T).toReal ≤ (B.gamma.measure u T).toReal ∧
      (B.gamma.measure u T).toReal ≤ hi * (A.gamma.measure u T).toReal := by
  apply aux_lem_endpoints_support_6_local_measure_bounds (centeredCube z r hr) A.form B.form A.core B.core
    hdom A.gamma B.gamma q hq hqQ lo hi hlo hhi _ _ u hu T hTq
  · intro v hv
    apply (aux_lem_endpoints_support_6_side_local_form_le hS A B RB q hq hqQ hi _ v hv).2
    filter_upwards [hweight1] with n hn
    exact lem_endpoints_support_6 _ _ rho hn q hi (fun x hx => (hb x hx).2)
  · intro v hv
    apply (aux_lem_endpoints_support_6_side_local_form_le hS B A RA q hq hqQ lo⁻¹ _ v hv).2
    filter_upwards [hweight2] with n hn
    exact aux_lem_endpoints_support_7_coefficient_weight_lower _ _ rho hn q lo hlo (fun x hx => (hb x hx).1)

theorem aux_lem_endpoints_support_7_side_weight_energy
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (A : aux_lem_endpoints_support_6_limit_side d hd model H om z r hr S G N1)
    (B : aux_lem_endpoints_support_6_limit_side d hd model H om' z r hr S G' N2)
    (RA : aux_lem_endpoints_support_6_resp_side d model H om z r hr S G N2)
    (RB : aux_lem_endpoints_support_6_resp_side d model H om' z r hr S G' N1)
    (rho : C(SpatialCoordinates d, ℝ)) (hpos : ∀ x, 0 < rho x)
    (hweight1 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N1 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N1 n) z hr).val x)
    (hweight2 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N2 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N2 n) z hr).val x) :
    ∀ u ∈ A.form.domain, B.form.form u u = ∫ x, rho x ∂(A.gamma.measure u) := by
  have hdom := aux_lem_endpoints_support_7_side_weight_domain A B RA RB rho hpos hweight1 hweight2
  have hdomA := aux_lem_endpoints_support_6_domain_eq_of_energy A.form.toClosedForm G A.energy_eq
  have hdomB := aux_lem_endpoints_support_6_domain_eq_of_energy B.form.toClosedForm G' B.energy_eq
  obtain ⟨lo, hi, hlo, _hhi, hb⟩ := aux_lem_endpoints_support_6_weight_compact_bounds z r hr rho hpos
  have hmeasure : ∀ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
      (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) → (∃ k : ℤ, rq = (3 : ℝ) ^ k) →
      (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ u : DomainL2 (centeredCube z r hr), MemFormCore G u →
      ∀ T : Set (SpatialCoordinates d), MeasurableSet T →
        T ⊆ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) →
        sInf (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
            (A.gamma.measure u T).toReal ≤ (B.gamma.measure u T).toReal ∧
          (B.gamma.measure u T).toReal ≤
            sSup (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
              (A.gamma.measure u T).toReal := by
    intro zq rq hrq _hRat _hTri hqQ u hu T _hT hTq
    let q : Set (SpatialCoordinates d) := centeredCube zq rq hrq
    have hne : (rho '' q).Nonempty := ⟨rho zq, ⟨zq, Metric.mem_ball_self (half_pos hrq), rfl⟩⟩
    have hbelow : BddBelow (rho '' q) :=
      ⟨lo, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact (hb x (subset_closure (hqQ hx))).1⟩
    have habove : BddAbove (rho '' q) :=
      ⟨hi, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact (hb x (subset_closure (hqQ hx))).2⟩
    have hmin : 0 < sInf (rho '' q) :=
      hlo.trans_le (le_csInf hne (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact (hb x (subset_closure (hqQ hx))).1))
    have hmax : 0 ≤ sSup (rho '' q) :=
      (hpos zq).le.trans (le_csSup habove ⟨zq, Metric.mem_ball_self (half_pos hrq), rfl⟩)
    have hucore : A.form.toClosedForm.MemCore u := by
      obtain ⟨huG, uc, huc, hucs, _hucQ, huae⟩ := hu
      exact ⟨aux_lem_endpoints_support_6_domain_mem_of_energy A.form.toClosedForm G A.energy_eq huG, uc, huc, hucs, subset_univ _, huae⟩
    exact aux_lem_endpoints_support_7_side_weight_local_bounds hS A B RA RB rho hdom hweight1 hweight2 q
      (centeredCube zq rq hrq).isOpen hqQ _ _ hmin hmax
      (fun x hx => ⟨csInf_le hbelow ⟨x, hx, rfl⟩, le_csSup habove ⟨x, hx, rfl⟩⟩)
      u hucore T hTq
  have hid := prop_21_catalog_global_weighted_energy z r hr rfl A.form.toClosedForm
    B.form.toClosedForm G G' A.energy_eq B.energy_eq A.gamma B.gamma rho
    rho.continuous.continuousOn (fun x _ => hpos x)
    (by rw [← hdomA, ← hdomB, hdom])
    (fun u hu => hdom ▸ (aux_lem_endpoints_support_6_domain_mem_of_energy A.form.toClosedForm G A.energy_eq hu.1)) hmeasure
    (aux_lem_endpoints_support_6_core_dense_of_isCoreOn (centeredCube z r hr) A.form.toClosedForm G A.energy_eq A.core)
  intro u hu
  have h := hid u (hdomA ▸ hu)
  have huB : u ∈ B.form.domain := hdom ▸ hu
  rw [← B.energy_eq, B.form.toClosedForm.energy_of_mem huB, EReal.coe_eq_coe_iff] at h
  obtain ⟨C, hC⟩ := A.core
  have hsupp := aux_lem_endpoints_support_2_energy_measure_support A.gamma
    (centeredCube z r hr).isOpen.measurableSet hC hu
  rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)] at h
  exact h

end Weight
end SubdiffusiveProcess.Paper
end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess.Paper

theorem aux_lem_endpoints_support_7_energy_measure_zero
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}
    {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm mu} (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    {u : Lp ℝ 2 mu} (hu : u ∈ E.domain) (hzero : E.form u u = 0) :
    Gamma.measure u = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have h : (Gamma.measure u univ).toReal = 0 := (Gamma.measure_univ u hu).trans hzero
  exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (Gamma.measure_ne_top hu univ)

theorem aux_lem_endpoints_support_7_supported_weight_integrable
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (rho : C(SpatialCoordinates d, ℝ)) (u : DomainL2 (centeredCube z r hr))
    (hu : u ∈ E.domain) : Integrable rho (Gamma.measure u) := by
  have : IsFiniteMeasure (Gamma.measure u) := ⟨Gamma.measure_univ_lt_top u hu⟩
  obtain ⟨C, hC⟩ := hcore
  have hsupp := aux_lem_endpoints_support_2_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC hu
  have hfull : ∀ᵐ x ∂Gamma.measure u,
      x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (ae_iff.mpr hsupp).mono (fun _ hx => subset_closure hx)
  have hint := rho.continuous.continuousOn.integrableOn_compact
    (lane2_isCompact_closure_centeredCube z hr) (μ := Gamma.measure u)
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hfull] at hint
  exact hint

section Order
variable {d : ℕ} (Q : Opens (SpatialCoordinates d))
  (E F Ew Fw : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
  (hdom : E.domain = F.domain)
  (hEwdom : Ew.domain = E.domain) (hFwdom : Fw.domain = F.domain)
  (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
  (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
  (rho : SpatialCoordinates d → ℝ)
  (hEw : ∀ u ∈ E.domain, Ew.form u u = ∫ x, rho x ∂(GammaE.measure u))
  (hFw : ∀ u ∈ F.domain, Fw.form u u = ∫ x, rho x ∂(GammaF.measure u))
include hdom hEwdom hFwdom GammaE GammaF hEw hFw

theorem aux_lem_endpoints_support_7_diagonal_weight_lower
    (hFcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hrho : ∀ x, 0 ≤ rho x)
    (hint : ∀ u ∈ F.domain, Integrable rho (GammaF.measure u))
    (c : ℝ) (horder : ∀ u ∈ E.domain, c * E.form u u ≤ F.form u u) :
    ∀ u ∈ Ew.domain, c * Ew.form u u ≤ Fw.form u u := by
  intro u hu
  have huE : u ∈ E.domain := hEwdom ▸ hu
  have huF : u ∈ F.domain := hdom ▸ huE
  have huFw : u ∈ Fw.domain := hFwdom.symm ▸ huF
  by_cases hc : 0 < c
  · have : IsFiniteMeasure (GammaE.measure u) := ⟨GammaE.measure_univ_lt_top u huE⟩
    have : IsFiniteMeasure (GammaF.measure u) := ⟨GammaF.measure_univ_lt_top u huF⟩
    rw [hEw u huE, hFw u huF]
    exact aux_lem_endpoints_support_6_weighted_integral_order (GammaE.measure u) (GammaF.measure u) c hc.le
      (aux_lem_endpoints_support_2_endpoint_invariance_energy_order_one_sided_light
        Q E F hFcore hdom GammaE GammaF c hc horder u huE)
      rho (Eventually.of_forall hrho) (hint u huF)
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hc) (Ew.form_nonneg u hu)).trans
      (Fw.form_nonneg u huFw)

theorem aux_lem_endpoints_support_7_diagonal_weight_upper
    (hEcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hrho : ∀ x, 0 ≤ rho x)
    (hint : ∀ u ∈ E.domain, Integrable rho (GammaE.measure u))
    (c : ℝ) (horder : ∀ u ∈ E.domain, F.form u u ≤ c * E.form u u) :
    ∀ u ∈ Ew.domain, Fw.form u u ≤ c * Ew.form u u := by
  by_cases hc : 0 < c
  · have hreverse : ∀ u ∈ F.domain, c⁻¹ * F.form u u ≤ E.form u u := by
      intro u hu
      exact (inv_mul_le_iff₀ hc).mpr (horder u (hdom ▸ hu))
    have hw := aux_lem_endpoints_support_7_diagonal_weight_lower Q F E Fw Ew hdom.symm hFwdom hEwdom
      GammaF GammaE rho hFw hEw hEcore hrho hint c⁻¹ hreverse
    intro u hu
    have huFw : u ∈ Fw.domain := hFwdom.symm ▸ (hdom ▸ (hEwdom ▸ hu))
    exact (inv_mul_le_iff₀ hc).mp (hw u huFw)
  · intro u hu
    have huE : u ∈ E.domain := hEwdom ▸ hu
    have huF : u ∈ F.domain := hdom ▸ huE
    have hc0 : c ≤ 0 := le_of_not_gt hc
    have hFzero : F.form u u = 0 := le_antisymm
      ((horder u huE).trans (mul_nonpos_of_nonpos_of_nonneg hc0 (E.form_nonneg u huE)))
      (F.form_nonneg u huF)
    have hFwzero : Fw.form u u = 0 := by
      rw [hFw u huF, aux_lem_endpoints_support_7_energy_measure_zero GammaF huF hFzero, integral_zero_measure]
    rw [hFwzero]
    by_cases hcEq : c = 0
    · rw [hcEq, zero_mul]
    · have hcNeg : c < 0 := lt_of_le_of_ne hc0 hcEq
      have hEzero : E.form u u = 0 := by
        have hh := horder u huE
        rw [hFzero] at hh
        nlinarith [E.form_nonneg u huE]
      have hEwzero : Ew.form u u = 0 := by
        rw [hEw u huE, aux_lem_endpoints_support_7_energy_measure_zero GammaE huE hEzero, integral_zero_measure]
      rw [hEwzero, mul_zero]

end Order


theorem aux_lem_endpoints_support_7_goodSeq_compare
    {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {Omega : Type}
    (GE GF : (i : ℕ) → Omega →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (c : ℝ) (hc : 1 ≤ c) (om : Omega)
    (hgood : aux_lem_endpoints_support_4_goodSeq z r hr GE GF c om) :
    aux_lem_endpoints_compare z r hr GE GF c om := by
  have hsn := aux_lem_endpoints_support_4_goodSeq_symm_pos z r hr GE GF c om hgood
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hEF := (aux_lem_endpoints_support_4_upperTest_iff z r hr GE GF om
    (fun i => (hsn i).1.1) (fun i => (hsn i).1.2) c hcpos.le).mp hgood.2.2.1
  have hFE := (aux_lem_endpoints_support_4_upperTest_iff z r hr GF GE om
    (fun i => (hsn i).2.1) (fun i => (hsn i).2.2) c hcpos.le).mp hgood.2.2.2.1
  intro i
  have hsubEF : limitFormDomain (GE i om) ⊆ limitFormDomain (GF i om) :=
    fun u hu => (hEF i u hu).trans_lt (EReal.coe_lt_top _)
  have hsubFE : limitFormDomain (GF i om) ⊆ limitFormDomain (GE i om) :=
    fun u hu => (hFE i u hu).trans_lt (EReal.coe_lt_top _)
  refine ⟨Subset.antisymm hsubEF hsubFE, ?_⟩
  intro u hu
  have hupper := hEF i u hu
  have hlower := hFE i u (hsubEF hu)
  rw [aux_lem_endpoints_support_3_energy_coe (GF i om) u (hsubEF hu)] at hupper
  rw [aux_lem_endpoints_support_3_energy_coe (GE i om) u hu] at hlower
  exact ⟨(inv_mul_le_iff₀ hcpos).mpr (EReal.coe_le_coe_iff.mp hlower),
    EReal.coe_le_coe_iff.mp hupper⟩

theorem aux_lem_endpoints_support_7_pair_weight_orders
    {d : ℕ} {hd : 2 ≤ d} {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} {om om' : BilateralField d}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {GE GF GE' GF' : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    {NE1 NE2 NF1 NF2 : ℕ → ℕ}
    (AE : aux_lem_endpoints_support_6_limit_side d hd model H om z r hr S GE NE1)
    (AF : aux_lem_endpoints_support_6_limit_side d hd model H om z r hr S GF NF1)
    (BE : aux_lem_endpoints_support_6_limit_side d hd model H om' z r hr S GE' NE2)
    (BF : aux_lem_endpoints_support_6_limit_side d hd model H om' z r hr S GF' NF2)
    (RAE : aux_lem_endpoints_support_6_resp_side d model H om z r hr S GE NE2)
    (RAF : aux_lem_endpoints_support_6_resp_side d model H om z r hr S GF NF2)
    (RBE : aux_lem_endpoints_support_6_resp_side d model H om' z r hr S GE' NE1)
    (RBF : aux_lem_endpoints_support_6_resp_side d model H om' z r hr S GF' NF1)
    (hdom : limitFormDomain GE = limitFormDomain GF)
    (rho : C(SpatialCoordinates d, ℝ)) (hpos : ∀ x, 0 < rho x)
    (hweightE1 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (NE1 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NE1 n) z hr).val x)
    (hweightE2 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (NE2 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NE2 n) z hr).val x)
    (hweightF1 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (NF1 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NF1 n) z hr).val x)
    (hweightF2 : ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (NF2 n) z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NF2 n) z hr).val x)
    (c : ℝ) :
    ((∀ u ∈ limitFormDomain GE,
      c * (limitFormEnergy GE u).toReal ≤ (limitFormEnergy GF u).toReal) →
      ∀ u ∈ limitFormDomain GE',
        c * (limitFormEnergy GE' u).toReal ≤ (limitFormEnergy GF' u).toReal) ∧
    ((∀ u ∈ limitFormDomain GE,
      (limitFormEnergy GF u).toReal ≤ c * (limitFormEnergy GE u).toReal) →
      ∀ u ∈ limitFormDomain GE',
        (limitFormEnergy GF' u).toReal ≤ c * (limitFormEnergy GE' u).toReal) := by
  have hAE := aux_lem_endpoints_support_6_domain_eq_of_energy AE.form.toClosedForm GE AE.energy_eq
  have hAF := aux_lem_endpoints_support_6_domain_eq_of_energy AF.form.toClosedForm GF AF.energy_eq
  have hBE := aux_lem_endpoints_support_6_domain_eq_of_energy BE.form.toClosedForm GE' BE.energy_eq
  have hBF := aux_lem_endpoints_support_6_domain_eq_of_energy BF.form.toClosedForm GF' BF.energy_eq
  have hdomA : AE.form.domain = AF.form.domain := by
    apply SetLike.coe_injective
    exact hAE.trans (hdom.trans hAF.symm)
  have hdomE := aux_lem_endpoints_support_7_side_weight_domain AE BE RAE RBE rho hpos hweightE1 hweightE2
  have hdomF := aux_lem_endpoints_support_7_side_weight_domain AF BF RAF RBF rho hpos hweightF1 hweightF2
  have hEweight := aux_lem_endpoints_support_7_side_weight_energy hS AE BE RAE RBE rho hpos hweightE1 hweightE2
  have hFweight := aux_lem_endpoints_support_7_side_weight_energy hS AF BF RAF RBF rho hpos hweightF1 hweightF2
  have hconvertE (u : DomainL2 (centeredCube z r hr)) (hu : u ∈ AE.form.domain) :
      AE.form.form u u = (limitFormEnergy GE u).toReal :=
    aux_lem_endpoints_support_6_form_eq_toReal_energy AE.form.toClosedForm GE AE.energy_eq u hu
  have hconvertF (u : DomainL2 (centeredCube z r hr)) (hu : u ∈ AE.form.domain) :
      AF.form.form u u = (limitFormEnergy GF u).toReal :=
    aux_lem_endpoints_support_6_form_eq_toReal_energy AF.form.toClosedForm GF AF.energy_eq u (hdomA ▸ hu)
  have hconvertBE (u : DomainL2 (centeredCube z r hr)) (hu : u ∈ BE.form.domain) :
      BE.form.form u u = (limitFormEnergy GE' u).toReal :=
    aux_lem_endpoints_support_6_form_eq_toReal_energy BE.form.toClosedForm GE' BE.energy_eq u hu
  have hconvertBF (u : DomainL2 (centeredCube z r hr)) (hu : u ∈ BE.form.domain) :
      BF.form.form u u = (limitFormEnergy GF' u).toReal :=
    aux_lem_endpoints_support_6_form_eq_toReal_energy BF.form.toClosedForm GF' BF.energy_eq u
      (hdomF ▸ (hdomA ▸ (hdomE.symm ▸ hu)))
  constructor
  · intro horder
    have horderA : ∀ u ∈ AE.form.domain, c * AE.form.form u u ≤ AF.form.form u u := by
      intro u hu
      rw [hconvertE u hu, hconvertF u hu]
      exact horder u (hAE ▸ hu)
    have hweighted := aux_lem_endpoints_support_7_diagonal_weight_lower (centeredCube z r hr)
      AE.form AF.form BE.form BF.form hdomA hdomE.symm hdomF.symm AE.gamma AF.gamma rho
      hEweight hFweight AF.core (fun x => (hpos x).le)
      (aux_lem_endpoints_support_7_supported_weight_integrable z r hr AF.form.toClosedForm AF.gamma AF.core rho)
      c horderA
    intro u hu
    have huBE : u ∈ BE.form.domain := aux_lem_endpoints_support_6_domain_mem_of_energy BE.form.toClosedForm GE' BE.energy_eq hu
    simpa only [hconvertBE u huBE, hconvertBF u huBE] using hweighted u huBE

  · intro horder
    have horderA : ∀ u ∈ AE.form.domain, AF.form.form u u ≤ c * AE.form.form u u := by
      intro u hu
      rw [hconvertE u hu, hconvertF u hu]
      exact horder u (hAE ▸ hu)
    have hweighted := aux_lem_endpoints_support_7_diagonal_weight_upper (centeredCube z r hr)
      AE.form AF.form BE.form BF.form hdomA hdomE.symm hdomF.symm AE.gamma AF.gamma rho
      hEweight hFweight AE.core (fun x => (hpos x).le)
      (aux_lem_endpoints_support_7_supported_weight_integrable z r hr AE.form.toClosedForm AE.gamma AE.core rho)
      c horderA
    intro u hu
    have huBE : u ∈ BE.form.domain := aux_lem_endpoints_support_6_domain_mem_of_energy BE.form.toClosedForm GE' BE.energy_eq hu
    simpa only [hconvertBE u huBE, hconvertBF u huBE] using hweighted u huBE

theorem aux_lem_endpoints_support_7_coefficient_weight_reverse
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (a b : PositiveCoefficient Q)
    (rho : SpatialCoordinates d → ℝ) (hpos : ∀ x, 0 < rho x)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x) :
    a.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => (rho x)⁻¹ * b.val x := by
  filter_upwards [hweight] with x hx
  rw [hx, inv_mul_cancel_left₀ (ne_of_gt (hpos x))]

theorem aux_lem_endpoints_support_7_endpoints_of_common_weight
    {d : ℕ} {hd : 2 ≤ d} {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (hS : ∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE1 NE2 NF1 NF2 : ℕ → ℕ → ℕ) (om om' : BilateralField d)
    (AE : ∀ i, aux_lem_endpoints_support_6_limit_side d hd model H om (z i) (r i) (hr i) (S i) (GE i om) (NE1 i))
    (AF : ∀ i, aux_lem_endpoints_support_6_limit_side d hd model H om (z i) (r i) (hr i) (S i) (GF i om) (NF1 i))
    (BE : ∀ i, aux_lem_endpoints_support_6_limit_side d hd model H om' (z i) (r i) (hr i) (S i) (GE i om') (NE2 i))
    (BF : ∀ i, aux_lem_endpoints_support_6_limit_side d hd model H om' (z i) (r i) (hr i) (S i) (GF i om') (NF2 i))
    (RAE : ∀ i, aux_lem_endpoints_support_6_resp_side d model H om (z i) (r i) (hr i) (S i) (GE i om) (NE2 i))
    (RAF : ∀ i, aux_lem_endpoints_support_6_resp_side d model H om (z i) (r i) (hr i) (S i) (GF i om) (NF2 i))
    (RBE : ∀ i, aux_lem_endpoints_support_6_resp_side d model H om' (z i) (r i) (hr i) (S i) (GE i om') (NE1 i))
    (RBF : ∀ i, aux_lem_endpoints_support_6_resp_side d model H om' (z i) (r i) (hr i) (S i) (GF i om') (NF1 i))
    (hdom : ∀ i, limitFormDomain (GE i om) = limitFormDomain (GF i om))
    (hdom' : ∀ i, limitFormDomain (GE i om') = limitFormDomain (GF i om'))
    (rho : C(SpatialCoordinates d, ℝ)) (hpos : ∀ x, 0 < rho x)
    (hweightE1 : ∀ i, ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (NE1 i n) (z i) (hr i)).val
        =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NE1 i n) (z i) (hr i)).val x)
    (hweightE2 : ∀ i, ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (NE2 i n) (z i) (hr i)).val
        =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NE2 i n) (z i) (hr i)).val x)
    (hweightF1 : ∀ i, ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (NF1 i n) (z i) (hr i)).val
        =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NF1 i n) (z i) (hr i)).val x)
    (hweightF2 : ∀ i, ∀ᶠ n in atTop,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (NF2 i n) (z i) (hr i)).val
        =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
        fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NF2 i n) (z i) (hr i)).val x) :
    sSup (aux_lem_endpoints_lowerSet z r hr GE GF om) =
        sSup (aux_lem_endpoints_lowerSet z r hr GE GF om') ∧
      sInf (aux_lem_endpoints_upperSet z r hr GE GF om) =
        sInf (aux_lem_endpoints_upperSet z r hr GE GF om') := by
  let rhoInv : C(SpatialCoordinates d, ℝ) :=
    ⟨fun x => (rho x)⁻¹, rho.continuous.inv₀ (fun x => ne_of_gt (hpos x))⟩
  have hInvPos : ∀ x, 0 < rhoInv x := fun x => inv_pos.mpr (hpos x)
  have hreverse (i : ℕ) (N : ℕ → ℕ)
      (h : ∀ᶠ n in atTop,
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N n) (z i) (hr i)).val
          =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
          fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) (z i) (hr i)).val x) :
      ∀ᶠ n in atTop,
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) (z i) (hr i)).val
          =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
          fun x => rhoInv x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om' (N n) (z i) (hr i)).val x := by
    filter_upwards [h] with n hn
    exact aux_lem_endpoints_support_7_coefficient_weight_reverse _ _ rho hpos hn
  have hf (i : ℕ) (c : ℝ) := aux_lem_endpoints_support_7_pair_weight_orders (hS i)
    (AE i) (AF i) (BE i) (BF i) (RAE i) (RAF i) (RBE i) (RBF i) (hdom i) rho hpos
    (hweightE1 i) (hweightE2 i) (hweightF1 i) (hweightF2 i) c
  have hb (i : ℕ) (c : ℝ) := aux_lem_endpoints_support_7_pair_weight_orders (hS i)
    (BE i) (BF i) (AE i) (AF i) (RBE i) (RBF i) (RAE i) (RAF i) (hdom' i) rhoInv hInvPos
    (hreverse i _ (hweightE2 i)) (hreverse i _ (hweightE1 i))
    (hreverse i _ (hweightF2 i)) (hreverse i _ (hweightF1 i)) c
  have hL : aux_lem_endpoints_lowerSet z r hr GE GF om = aux_lem_endpoints_lowerSet z r hr GE GF om' := by
    ext c
    constructor
    · intro hc i
      exact (hf i c).1 (hc i)
    · intro hc i
      exact (hb i c).1 (hc i)
  have hU : aux_lem_endpoints_upperSet z r hr GE GF om = aux_lem_endpoints_upperSet z r hr GE GF om' := by
    ext c
    constructor
    · intro hc i
      exact (hf i c).2 (hc i)
    · intro hc i
      exact (hb i c).2 (hc i)
  exact ⟨congrArg sSup hL, congrArg sInf hU⟩

end SubdiffusiveProcess.Paper
end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess.Paper

theorem aux_lem_endpoints_support_7_endpoint_invariance_with_sides
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hJoint : in_joint_extracted_candidates d model H (BilateralField d)
      (chaosSampleLaw model).toMeasure (fun omega => omega) z r hr Sspace GN GE GF NE NF)
    (hside : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
      (∃ σ : ℕ → ℕ, StrictMono σ ∧
        Nonempty (aux_lem_endpoints_support_6_limit_side d hd model H omega (z i) (r i) (hr i)
          (Sspace i) (GE i omega) (NE ∘ σ))) ∧
      (∃ σ : ℕ → ℕ, StrictMono σ ∧
        Nonempty (aux_lem_endpoints_support_6_limit_side d hd model H omega (z i) (r i) (hr i)
          (Sspace i) (GF i omega) (NF ∘ σ))))
    (hdomains : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
      limitFormDomain (GE i omega) = limitFormDomain (GF i omega)) :
    (∀ S : Finset ℤ,
      ∀ᵐ zz ∂((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure),
        sSup (aux_lem_endpoints_lowerSet z r hr GE GF zz.1) =
          sSup (aux_lem_endpoints_lowerSet z r hr GE GF
            (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2))) ∧
    (∀ S : Finset ℤ,
      ∀ᵐ zz ∂((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure),
        sInf (aux_lem_endpoints_upperSet z r hr GE GF zz.1) =
          sInf (aux_lem_endpoints_upperSet z r hr GE GF
            (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2))) := by
  classical
  have hgood := (((hJoint.2.2.2.1.2.and hside).and hdomains).and hJoint.2.2.2.2.2.2.2)
  have hfst : MeasurePreserving (Prod.fst : BilateralField d × BilateralField d → BilateralField d)
      ((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure)
      (chaosSampleLaw model).toMeasure := measurePreserving_fst
  have hgoodfst := ae_of_ae_map hfst.measurable.aemeasurable
    (by rw [hfst.map_eq]; exact hgood)
  have heq : ∀ S : Finset ℤ,
      ∀ᵐ zz ∂((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure),
        sSup (aux_lem_endpoints_lowerSet z r hr GE GF zz.1) =
            sSup (aux_lem_endpoints_lowerSet z r hr GE GF
              (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2)) ∧
          sInf (aux_lem_endpoints_upperSet z r hr GE GF zz.1) =
            sInf (aux_lem_endpoints_upperSet z r hr GE GF
              (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2)) := by
    intro S
    have hgoodres := aux_lem_endpoints_support_4_endpoint_invariance_ae_resample model S hgood
    filter_upwards [hgoodfst, hgoodres] with zz hfirst hsecond
    have hshift := aux_lem_endpoints_support_4_endpoint_invariance_H_shift S zz.1 zz.2 H
      hfirst.1.1.1 hsecond.1.1.1
    let rho : C(SpatialCoordinates d, ℝ) :=
      ⟨fun x => Real.exp (aux_lem_endpoints_support_4_endpoint_invariance_weight S zz.1 zz.2 x),
        Real.continuous_exp.comp (aux_lem_endpoints_support_4_endpoint_invariance_weight S zz.1 zz.2).continuous⟩
    have hpos : ∀ x, 0 < rho x := fun x => Real.exp_pos _
    have hNE := hJoint.2.2.2.2.1.1.tendsto_atTop.eventually
      (eventually_ge_atTop (aux_lem_endpoints_support_3_endpoint_invariance_N0 S))
    have hNF := hJoint.2.2.2.2.1.2.tendsto_atTop.eventually
      (eventually_ge_atTop (aux_lem_endpoints_support_3_endpoint_invariance_N0 S))
    have key (i : ℕ) (N : ℕ → ℕ)
        (hN : ∀ᶠ n in atTop, aux_lem_endpoints_support_3_endpoint_invariance_N0 S ≤ N n) :
        ∀ᶠ n in atTop,
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H
            (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2) (N n) (z i) (hr i)).val
            =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
            fun x => rho x * (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H zz.1 (N n) (z i) (hr i)).val x := by
      filter_upwards [hN] with n hn
      have he := aux_lem_endpoints_support_4_endpoint_invariance_cutoffPositiveCoefficient_eq S zz.1 zz.2
        model H hshift hn (z i) (r i) (hr i)
      filter_upwards [he, ae_restrict_mem (centeredCube (z i) (r i) (hr i)).isOpen.measurableSet]
        with x hx hxQ
      exact hx hxQ
    have hE1 := fun i => Classical.choose_spec (hfirst.1.1.2 i).1
    have hF1 := fun i => Classical.choose_spec (hfirst.1.1.2 i).2
    have hE2 := fun i => Classical.choose_spec (hsecond.1.1.2 i).1
    have hF2 := fun i => Classical.choose_spec (hsecond.1.1.2 i).2
    apply aux_lem_endpoints_support_7_endpoints_of_common_weight z r hr Sspace hJoint.2.2.2.2.2.1 GE GF
      (fun i => NE ∘ Classical.choose (hfirst.1.1.2 i).1)
      (fun i => NE ∘ Classical.choose (hsecond.1.1.2 i).1)
      (fun i => NF ∘ Classical.choose (hfirst.1.1.2 i).2)
      (fun i => NF ∘ Classical.choose (hsecond.1.1.2 i).2)
      zz.1 (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2)
      (fun i => Classical.choice (hE1 i).2)
      (fun i => Classical.choice (hF1 i).2)
      (fun i => Classical.choice (hE2 i).2)
      (fun i => Classical.choice (hF2 i).2)
      (fun i => aux_lem_endpoints_support_6_resp_side_of_tendsto NE
        (fun n => GN i (NE n) zz.1) (fun n f => hJoint.2.2.2.2.2.2.1 i (NE n) zz.1 f)
        (hfirst.2 i).1 (hE2 i).1)
      (fun i => aux_lem_endpoints_support_6_resp_side_of_tendsto NF
        (fun n => GN i (NF n) zz.1) (fun n f => hJoint.2.2.2.2.2.2.1 i (NF n) zz.1 f)
        (hfirst.2 i).2 (hF2 i).1)
      (fun i => aux_lem_endpoints_support_6_resp_side_of_tendsto NE
        (fun n => GN i (NE n)
          (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2))
        (fun n f => hJoint.2.2.2.2.2.2.1 i (NE n)
          (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2) f)
        (hsecond.2 i).1 (hE1 i).1)
      (fun i => aux_lem_endpoints_support_6_resp_side_of_tendsto NF
        (fun n => GN i (NF n)
          (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2))
        (fun n f => hJoint.2.2.2.2.2.2.1 i (NF n)
          (aux_lem_endpoints_support_3_endpoint_invariance_resample S zz.1 zz.2) f)
        (hsecond.2 i).2 (hF1 i).1)
      hfirst.1.2 hsecond.1.2 rho hpos
    · intro i
      exact key i _ ((hE1 i).1.tendsto_atTop.eventually hNE)
    · intro i
      exact key i _ ((hE2 i).1.tendsto_atTop.eventually hNE)
    · intro i
      exact key i _ ((hF1 i).1.tendsto_atTop.eventually hNF)
    · intro i
      exact key i _ ((hF2 i).1.tendsto_atTop.eventually hNF)
  exact ⟨fun S => (heq S).mono (fun _ h => h.1), fun S => (heq S).mono (fun _ h => h.2)⟩

end SubdiffusiveProcess.Paper
end

namespace SubdiffusiveProcess.Paper

theorem lem_endpoints_support_7
    {d : ℕ} (hd : 2 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om n z0 hr0) v v ≤
            responseForm Sspace0
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om n z0 hr0) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N0 : ℕ → ℕ)
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N0 n) z0 hr0)
          ((sobolevVolumeLoad f).comp Sspace0.space.subtypeL)).val.1)
    (hGN0tendsto : Tendsto GN0 atTop (𝓝 G0))
    (hbundle0 : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 Sspace0 G0 N0)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F) :
    Nonempty (aux_lem_endpoints_support_6_limit_side d hd model H om z0 r0 hr0 Sspace0 G0 N0) := by
  obtain ⟨F, _hFdom, hF, hcore⟩ := aux_lem_endpoints_support_2_hregularity_side hd model H om z0 r0 hr0
    Sspace0 hSspace0 hcontract0 G0 N0 GN0 hGN0 hGN0tendsto hbundle0
  have hlocal := aux_lem_endpoints_support_2_form_core_locality d hd model H om z0 r0 hr0
    Sspace0 hSspace0 G0 N0 GN0 hGN0 hGN0tendsto hbundle0 F.toClosedForm hF
  have hstrong := (BD z0 r0 hr0 F).isStronglyLocal_of_onCore
    (aux_lem_endpoints_support_6_isRegular_of_core (centeredCube z0 r0 hr0) F.toClosedForm hcore)
    (BDQ z0 r0 hr0 F hcore hlocal)
  obtain ⟨Gamma, _hSupport⟩ := aux_lem_endpoints_support_6_energy_measure_of_locality z0 r0 hr0 F
    (EM z0 r0 hr0 F) hcore hstrong
  exact ⟨⟨GN0, hGN0, hGN0tendsto, hbundle0, F, hF, hcore, Gamma⟩⟩

end SubdiffusiveProcess.Paper
