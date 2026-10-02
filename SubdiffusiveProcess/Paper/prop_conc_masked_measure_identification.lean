import SubdiffusiveProcess.Paper.prop_conc_weighted_identification_bridge
import SubdiffusiveProcess.Paper.prop_conc_pair_mask
import SubdiffusiveProcess.Paper.prop_conc_weighted_measure_identification
import SubdiffusiveProcess.Paper.prop_conc_core_measure_data
import SubdiffusiveProcess.Paper.energy_order_of_form_order
import SubdiffusiveProcess.DirichletForm.LocalMinimizerUniqueness
import SubdiffusiveProcess.DirichletForm.KilledDomainOrder
import Mathlib.Tactic

/-! Deterministic identification of the local energy measures of the canonical masked pair with those of
a tied pair of the resampled environment.  Let `Y` be a pair of limiting forms on a padded cube `Q` with
observation cell `q`, and let `Yc` be a second such pair whose forms are the `exp w`-weighted forms of `Y`
(`Yc.E(u,u) = ∫ exp w dΓ_Y(u)`, likewise `F`).  Both have affine trace classes.  Then the canonical mask of
`Y` by `1_q w` and `Yc` have the same coordinate and `F`-minimizer energy measures on every measurable
subset of `q`, the same normalizers, and hence the same normalized measures `ν`, `ζ` on `q`; every ball
growth bound of `ν_Yc` transfers to the mask with the same constant.  No probabilistic assertion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace Paper
noncomputable section

section Measures

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}

/-- A zero-energy difference on a set makes the energy measures of the two functions agree on its
measurable subsets. -/
theorem aux_prop_conc_masked_measure_identification_eq_of_sub_zero
    {E : DirichletForm.ClosedForm mu} (Gamma : DirichletForm.EnergyMeasure E)
    {u v : Lp ℝ 2 mu} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    {q : Set X} (hq0 : Gamma.measure (u - v) q = 0)
    {A : Set X} (hA : MeasurableSet A) (hAq : A ⊆ q) :
    Gamma.measure u A = Gamma.measure v A := by
  have hd : u - v ∈ E.domain := E.domain.sub_mem hu hv
  have hAd : Gamma.measure (u - v) A = 0 :=
    le_antisymm ((measure_mono hAq).trans hq0.le) (zero_le _)
  have hcross : Gamma.cross u (u - v) A = 0 := by
    have h0 := Gamma.abs_cross_le u hu (u - v) hd A hA
    rw [hAd, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] at h0
    exact abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  have hcd : Gamma.cross (u - v) (u - v) A = 0 := by
    rw [Gamma.cross_self _ hd A hA, hAd]
    simp
  have hvv : v = u - (u - v) := by abel
  have hreal : (Gamma.measure v A).toReal = (Gamma.measure u A).toReal := by
    rw [← Gamma.cross_self v hv A hA, ← Gamma.cross_self u hu A hA]
    have hsub := Gamma.cross_sub_self_apply hu hd A
    rw [← hvv, hcross, hcd] at hsub
    simpa using hsub
  exact ((ENNReal.toReal_eq_toReal_iff' (Gamma.measure_ne_top hu A)
    (Gamma.measure_ne_top hv A)).mp hreal.symm)

/-- Two functions whose local energies vanish on `q` have zero local energy of their difference. -/
theorem aux_prop_conc_masked_measure_identification_sub_zero_of_zero
    {E : DirichletForm.ClosedForm mu} (Gamma : DirichletForm.EnergyMeasure E)
    {u v : Lp ℝ 2 mu} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    {q : Set X} (hq : MeasurableSet q)
    (hu0 : Gamma.measure u q = 0) (hv0 : Gamma.measure v q = 0) :
    Gamma.measure (u - v) q = 0 := by
  have hd : u - v ∈ E.domain := E.domain.sub_mem hu hv
  have hcross : Gamma.cross u v q = 0 := by
    have h0 := Gamma.abs_cross_le u hu v hv q hq
    rw [hu0, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at h0
    exact abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  have hsub := Gamma.cross_sub_self_apply hu hv q
  rw [Gamma.cross_self (u - v) hd q hq, Gamma.cross_self u hu q hq,
    Gamma.cross_self v hv q hq, hcross, hu0, hv0] at hsub
  simp only [ENNReal.toReal_zero, mul_zero, sub_zero, add_zero] at hsub
  exact (ENNReal.toReal_eq_zero_iff _).mp hsub |>.resolve_right (Gamma.measure_ne_top hd q)

end Measures

section Core

variable {d : ℕ}



theorem aux_prop_conc_masked_measure_identification_minimizer_sub_zero
    (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (D : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hD : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) D)
    (hcoerc : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ D, ‖v‖ ^ 2 ≤ K * E.form v v)
    (bv : SpatialCoordinates d → ℝ)
    (u1 u2 a1 a2 : DomainL2 (centeredCube zQ R hR))
    (hu1 : u1 ∈ E.domain) (hu2 : u2 ∈ E.domain) (ha1 : a1 ∈ E.domain) (ha2 : a2 ∈ E.domain)
    (U1 U2 : SpatialCoordinates d → ℝ)
    (hU1 : ContinuousOn U1 (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hU2 : ContinuousOn U2 (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hrep1 : ⇑u1 =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U1)
    (hrep2 : ⇑u2 =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U2)
    (hb1 : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), U1 x = bv x)
    (hb2 : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), U2 x = bv x)
    (hc1 : a1 - u1 ∈ D) (hc2 : a2 - u2 ∈ D)
    (hm1 : ∀ v ∈ E.domain, v - u1 ∈ D →
      (Gamma.measure a1 (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal ≤
        (Gamma.measure v (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal)
    (hm2 : ∀ v ∈ E.domain, v - u2 ∈ D →
      (Gamma.measure a2 (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal ≤
        (Gamma.measure v (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal) :
    Gamma.measure (a1 - a2) (centeredCube zq r hr : Set (SpatialCoordinates d)) = 0 := by
  classical
  let q : Set (SpatialCoordinates d) := (centeredCube zq r hr : Set (SpatialCoordinates d))
  have hqmeas : MeasurableSet q := (centeredCube zq r hr).isOpen.measurableSet
  let S := aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) E.toClosedForm Gamma q bv
  have hne : S.Nonempty := ⟨(Gamma.measure u1 q).toReal, u1, U1, hu1, hU1, hrep1, hb1, rfl⟩
  have hbdd : BddBelow S := ⟨0, by
    rintro e ⟨v, V, -, -, -, -, rfl⟩
    exact ENNReal.toReal_nonneg⟩
  have hglb : IsGLB S (sInf S) := isGLB_csInf hne hbdd
  -- the minimum over any class with a continuous representative is the glb
  have hleast : ∀ (u : DomainL2 (centeredCube zQ R hR)) (U : SpatialCoordinates d → ℝ),
      u ∈ E.domain →
      ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))) →
      (⇑u =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U) →
      (∀ x ∈ frontier q, U x = bv x) →
      IsLeast {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ D ∧
        t = (Gamma.measure (u + w) q).toReal} (sInf S) :=
    fun u U hu hU hrep hb => prop_conc_weighted_identification_bridge d hd zQ zq R r hR hr hqQ E
      Gamma hcore D hD hcoerc u hu U hU hrep bv hb (sInf S) hglb
  -- a minimizer of a class with a continuous representative has the glb as its value
  have key : ∀ (u a : DomainL2 (centeredCube zQ R hR)) (U : SpatialCoordinates d → ℝ),
      u ∈ E.domain →
      ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))) →
      (⇑u =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U) →
      (∀ x ∈ frontier q, U x = bv x) → a ∈ E.domain → a - u ∈ D →
      (∀ v ∈ E.domain, v - u ∈ D →
        (Gamma.measure a q).toReal ≤ (Gamma.measure v q).toReal) →
      (Gamma.measure a q).toReal = sInf S := by
    intro u a U hu hU hrep hb ha hau hmin
    have hl := hleast u U hu hU hrep hb
    have h1 : sInf S ≤ (Gamma.measure a q).toReal :=
      hl.2 ⟨a - u, hau, by rw [add_sub_cancel]⟩
    obtain ⟨w0, hw0, hw0eq⟩ := hl.1
    have hv0 : u + w0 ∈ E.domain := E.domain.add_mem hu (hD.le_domain hw0)
    have h2 := hmin (u + w0) hv0 (by rw [add_sub_cancel_left]; exact hw0)
    exact le_antisymm (h2.trans_eq hw0eq.symm) h1
  have hA1 := key u1 a1 U1 hu1 hU1 hrep1 hb1 ha1 hc1 hm1
  have hA2 := key u2 a2 U2 hu2 hU2 hrep2 hb2 ha2 hc2 hm2
  -- midpoint
  let umid : DomainL2 (centeredCube zQ R hR) := (1 / 2 : ℝ) • (u1 + u2)
  let amid : DomainL2 (centeredCube zQ R hR) := (1 / 2 : ℝ) • (a1 + a2)
  have humid : umid ∈ E.domain :=
    E.domain.smul_mem _ (E.domain.add_mem hu1 hu2)
  have hamid : amid ∈ E.domain := E.domain.smul_mem _ (E.domain.add_mem ha1 ha2)
  have hUmid : ContinuousOn (fun x => (1 / 2 : ℝ) * (U1 x + U2 x))
      (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))) :=
    continuousOn_const.mul (hU1.add hU2)
  have hrepmid : ⇑umid =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))]
      (fun x => (1 / 2 : ℝ) * (U1 x + U2 x)) := by
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (u1 + u2), Lp.coeFn_add u1 u2, hrep1, hrep2]
      with x hs ha h1 h2
    change ((1 / 2 : ℝ) • (u1 + u2)) x = _
    rw [hs, Pi.smul_apply, ha, Pi.add_apply, h1, h2, smul_eq_mul]
  have hbmid : ∀ x ∈ frontier q, (fun x => (1 / 2 : ℝ) * (U1 x + U2 x)) x = bv x := by
    intro x hx
    simp only [hb1 x hx, hb2 x hx]
    ring
  have hcmid : amid - umid ∈ D := by
    have : amid - umid = (1 / 2 : ℝ) • ((a1 - u1) + (a2 - u2)) := by
      simp only [amid, umid, smul_add, smul_sub]
      abel
    rw [this]
    exact D.smul_mem _ (D.add_mem hc1 hc2)
  have hmid : sInf S ≤ (Gamma.measure amid q).toReal :=
    (hleast umid _ humid hUmid hrepmid hbmid).2 ⟨amid - umid, hcmid, by rw [add_sub_cancel]⟩
  exact DirichletForm.EnergyMeasure.measure_sub_eq_zero_of_midpoint_minimal Gamma a1 a2 ha1 ha2 q
    hqmeas (hA1.trans_le hmid) (hA2.trans_le hmid)

end Core

section Weighted

variable {d : ℕ}

/-- Comparable forms on one domain share their killed domains. -/
theorem aux_prop_conc_masked_measure_identification_killed_transfer
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}
    (E F : DirichletForm.ClosedForm mu) (hdom : E.domain = F.domain)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hform : ∀ v ∈ E.domain, c * E.form v v ≤ F.form v v ∧ F.form v v ≤ C * E.form v v)
    (U : Set X) (D : Submodule ℝ (Lp ℝ 2 mu)) (hD : DirichletForm.IsKilledDomain E U D) :
    DirichletForm.IsKilledDomain F U D := by
  have h1 := DirichletForm.IsKilledDomain.eq_of_isKilledDomain hD
    (DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure E U)
  rw [h1, DirichletForm.ClosedForm.killedCoreClosure_eq_of_form_bounds E F hdom c C hc hC hform U]
  exact DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure F U

/-- A bounded measurable density compares the integral against a finite measure with its total mass. -/
theorem aux_prop_conc_masked_measure_identification_integral_bounds
    {X : Type*} [MeasurableSpace X] (nu : Measure X) [IsFiniteMeasure nu]
    (f : X → ℝ) (hf : Measurable f) (lo hi : ℝ) (hlo : ∀ x, lo ≤ f x) (hhi : ∀ x, f x ≤ hi) :
    lo * (nu Set.univ).toReal ≤ ∫ x, f x ∂nu ∧ ∫ x, f x ∂nu ≤ hi * (nu Set.univ).toReal := by
  have hint : Integrable f nu := by
    refine Integrable.mono' (integrable_const (max |lo| |hi|)) hf.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by
      have h1 := neg_abs_le lo
      have h2 := le_max_left |lo| |hi|
      linarith only [hlo x, h1, h2], by
      have h1 := le_abs_self hi
      have h2 := le_max_right |lo| |hi|
      linarith only [hhi x, h1, h2]⟩
  have hreal : (nu Set.univ).toReal = nu.real Set.univ := rfl
  constructor
  · have := integral_mono (integrable_const lo) hint hlo
    rw [integral_const, smul_eq_mul, mul_comm] at this
    rw [hreal, mul_comm]
    simpa only [Measure.real, smul_eq_mul, mul_comm] using this
  · have := integral_mono hint (integrable_const hi) hhi
    rw [integral_const, smul_eq_mul, mul_comm] at this
    rw [hreal, mul_comm]
    simpa only [Measure.real, smul_eq_mul, mul_comm] using this

/-- A form whose diagonal is the `exp w`-weighted diagonal of `E` (`w` continuous) is comparable with `E`,
and its energy measure is the weighted energy measure of `E` on subsets of the closed padded cube. -/
theorem aux_prop_conc_masked_measure_identification_weighted
    (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (E E' : _root_.DirichletForm
      (volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (Gamma' : DirichletForm.EnergyMeasure E'.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) C)
    (hcore' : ∃ C, DirichletForm.IsCoreOn E'.toClosedForm
      (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) C)
    (hloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (w : SpatialCoordinates d → ℝ) (hw : Continuous w)
    (hdom : E.domain = E'.domain)
    (hdiag : ∀ u ∈ E.domain, E'.form u u = ∫ x, Real.exp (w x) ∂(Gamma.measure u)) :
    (∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      A ⊆ closure (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) →
      Gamma'.measure u A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (w x)) ∂(Gamma.measure u)) ∧
    ∃ K : ℝ, ∀ v ∈ E.domain, Real.exp (-K) * E.form v v ≤ E'.form v v ∧
      E'.form v v ≤ Real.exp K * E.form v v := by
  classical
  let Q := centeredCube zQ RQ hRQ
  have hQmeas : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  have hcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) :=
    lane2_isCompact_closure_centeredCube zQ hRQ
  obtain ⟨C0, hC0⟩ := hcompact.exists_bound_of_continuousOn hw.continuousOn
  set K : ℝ := max C0 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  let gt : SpatialCoordinates d → ℝ := fun x => max (-K) (min K (w x))
  have hgt_meas : Measurable gt :=
    (continuous_const.max (continuous_const.min hw)).measurable
  have hgt_bound : ∀ x, |gt x| ≤ K := by
    intro x
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith only [hK0]) (min_le_left _ _)⟩
  have hgt_eq : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), gt x = w x := by
    intro x hx
    have hx1 : ‖w x‖ ≤ K := (hC0 x hx).trans (le_max_left _ _)
    have hx2 := abs_le.mp (by simpa only [Real.norm_eq_abs] using hx1)
    show max (-K) (min K (w x)) = w x
    rw [min_eq_right hx2.2, max_eq_right hx2.1]
  have hformgt : ∀ u ∈ E.domain, E'.form u u = ∫ x, Real.exp (gt x) ∂(Gamma.measure u) := by
    intro u hu
    rw [hdiag u hu]
    obtain ⟨Cc, hCc⟩ := hcore
    have hsupp : Gamma.measure u (Q : Set (SpatialCoordinates d))ᶜ = 0 :=
      aux_prop_conc_core_measure_data_energy_measure_support Gamma hQmeas hCc hu
    have hmem : ∀ᵐ x ∂Gamma.measure u, x ∈ (Q : Set (SpatialCoordinates d)) := ae_iff.mpr hsupp
    apply integral_congr_ae
    filter_upwards [hmem] with x hx
    rw [hgt_eq x (subset_closure hx)]
  have hmeas := (prop_conc_weighted_measure_identification Q E E' Gamma Gamma' hcore hcore'
    hloc hdom gt hgt_meas K hgt_bound hformgt).1
  refine ⟨?_, K, ?_⟩
  · intro u hu A hA hAQ
    rw [hmeas u hu A hA]
    apply setLIntegral_congr_fun hA
    intro x hx
    show ENNReal.ofReal (Real.exp (gt x)) = ENNReal.ofReal (Real.exp (w x))
    rw [hgt_eq x (hAQ hx)]
  · intro v hv
    letI : IsFiniteMeasure (Gamma.measure v) := ⟨Gamma.measure_univ_lt_top v hv⟩
    have hb := aux_prop_conc_masked_measure_identification_integral_bounds (Gamma.measure v)
      (fun x => Real.exp (gt x)) (Real.measurable_exp.comp hgt_meas) (Real.exp (-K)) (Real.exp K)
      (fun x => Real.exp_le_exp.mpr (abs_le.mp (hgt_bound x)).1)
      (fun x => Real.exp_le_exp.mpr (abs_le.mp (hgt_bound x)).2)
    rw [Gamma.measure_univ v hv] at hb
    rw [hformgt v hv]
    exact hb

end Weighted

section Mask

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
  {C0 m M : ℝ}

/-- What the canonical masked pair records about its domain, killed domain, weighted energy measures
and trace classes; read off from the construction. -/
theorem aux_prop_conc_masked_measure_identification_mask_facts
    (Y : prop_conc_pair_data Q z r hr C0 m M) (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    (aux_prop_conc_pair_mask_pair Y g hg K hK).D = Y.D ∧
    (aux_prop_conc_pair_mask_pair Y g hg K hK).E.domain = Y.E.domain ∧
    (aux_prop_conc_pair_mask_pair Y g hg K hK).F.domain = Y.F.domain ∧
    (∀ u ∈ Y.E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      (aux_prop_conc_pair_mask_pair Y g hg K hK).GammaE.measure u A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Y.GammaE.measure u)) ∧
    (∀ u ∈ Y.F.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      (aux_prop_conc_pair_mask_pair Y g hg K hK).GammaF.measure u A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Y.GammaF.measure u)) ∧
    (∀ p, (((aux_prop_conc_pair_mask_pair Y g hg K hK).P.boundary p : DomainL2 Q)) -
      (Y.P.boundary p : DomainL2 Q) ∈ Y.D) ∧
    (∀ p, (((aux_prop_conc_pair_mask_pair Y g hg K hK).P.uF p : DomainL2 Q)) -
      (Y.P.boundary p : DomainL2 Q) ∈ Y.D) := by
  let W := Classical.choice (aux_prop_conc_pair_mask_exists Y g hg K hK)
  exact ⟨rfl, W.Edata.domain_eq, W.Fdata.domain_eq, W.Edata.weight, W.Fdata.weight,
    fun p => W.traceEg p, fun p => W.traceFg p⟩

end Mask

section Main

variable {d : ℕ}

/-- The deterministic identification for an abstract masked pair `X` of `Y`: `X` has the mask facts
(killed domain, domains, weighted energy measures for a weight `g` agreeing with `w` on the cell, trace
classes) and `Yc` has the `exp w`-weighted forms of `Y`. -/
theorem aux_prop_conc_masked_measure_identification_core
    (hd : 2 ≤ d) (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc) (C0 m M : ℝ)
    (Y Yc X : prop_conc_pair_data (centeredCube zQ RQ hRQ) zc rc hrc C0 m M)
    (hYaff : aux_prop_conc_pair_data_affine Y) (hYcaff : aux_prop_conc_pair_data_affine Yc)
    (w g : SpatialCoordinates d → ℝ) (hw : Continuous w)
    (hgw : ∀ x ∈ (centeredCube zc rc hrc : Set (SpatialCoordinates d)), g x = w x)
    (hdomE : Y.E.domain = Yc.E.domain)
    (hdiagE : ∀ u ∈ Y.E.domain, Yc.E.form u u = ∫ x, Real.exp (w x) ∂(Y.GammaE.measure u))
    (hdiagF : ∀ u ∈ Y.F.domain, Yc.F.form u u = ∫ x, Real.exp (w x) ∂(Y.GammaF.measure u))
    (hXD : X.D = Y.D) (hXEd : X.E.domain = Y.E.domain) (hXFd : X.F.domain = Y.F.domain)
    (hXEw : ∀ u ∈ Y.E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      X.GammaE.measure u A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Y.GammaE.measure u))
    (hXFw : ∀ u ∈ Y.F.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      X.GammaF.measure u A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Y.GammaF.measure u))
    (hXbc : ∀ p, (X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) -
      (Y.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Y.D)
    (hXfc : ∀ p, (X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
      (Y.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Y.D) :
    (∀ p, X.P.QE p = Yc.P.QE p) ∧
    (∀ p (A : Set (SpatialCoordinates d)), MeasurableSet A →
      A ⊆ (centeredCube zc rc hrc : Set (SpatialCoordinates d)) →
      X.GammaE.measure (X.P.boundary p) A = Yc.GammaE.measure (Yc.P.boundary p) A) ∧
    (∀ p (A : Set (SpatialCoordinates d)), MeasurableSet A →
      A ⊆ (centeredCube zc rc hrc : Set (SpatialCoordinates d)) →
      X.GammaE.measure (X.P.uF p) A = Yc.GammaE.measure (Yc.P.uF p) A) ∧
    (∀ p (A : Set (SpatialCoordinates d)), MeasurableSet A →
      A ⊆ (centeredCube zc rc hrc : Set (SpatialCoordinates d)) →
      X.GammaE.measure ((X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
          (X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ))) A =
        Yc.GammaE.measure ((Yc.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
          (Yc.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ))) A) := by
  classical
  set q : Set (SpatialCoordinates d) := (centeredCube zc rc hrc : Set (SpatialCoordinates d)) with hqdef
  have hqmeas : MeasurableSet q := (centeredCube zc rc hrc).isOpen.measurableSet
  have hqQ : q ⊆ (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) :=
    subset_closure.trans Y.hinside
  have hqcl : q ⊆ closure (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) :=
    hqQ.trans subset_closure
  have hm0 : 0 < m := aux_prop_conc_pair_mask_mpos Y
  have hM0 : 0 ≤ M := hm0.le.trans Y.hmM
  have hdomF : Y.F.domain = Yc.F.domain :=
    Y.P.domain_eq.symm.trans (hdomE.trans Yc.P.domain_eq)
  obtain ⟨hmeasE, KE, hcompE⟩ := aux_prop_conc_masked_measure_identification_weighted zQ RQ hRQ
    Y.E Yc.E Y.GammaE Yc.GammaE Y.hEc Yc.hEc Y.hEl w hw hdomE hdiagE
  obtain ⟨hmeasF, KF, hcompF⟩ := aux_prop_conc_masked_measure_identification_weighted zQ RQ hRQ
    Y.F Yc.F Y.GammaF Yc.GammaF Y.hFc Yc.hFc Y.hFl w hw hdomF hdiagF
  -- killed domains of the tied pair are those of `Y`
  have hkE : DirichletForm.IsKilledDomain Yc.E.toClosedForm q Y.D :=
    aux_prop_conc_masked_measure_identification_killed_transfer Y.E.toClosedForm Yc.E.toClosedForm
      hdomE (Real.exp (-KE)) (Real.exp KE) (Real.exp_pos _) (Real.exp_pos _).le hcompE q Y.D
      Y.P.killed
  have hDeq : Yc.D = Y.D :=
    DirichletForm.IsKilledDomain.eq_of_isKilledDomain Yc.P.killed hkE
  have hkF : DirichletForm.IsKilledDomain Yc.F.toClosedForm q Y.D :=
    aux_prop_conc_masked_measure_identification_killed_transfer Yc.E.toClosedForm
      Yc.F.toClosedForm Yc.P.domain_eq m M hm0 hM0 Yc.horder q Y.D hkE
  have hcoE : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ Y.D, ‖v‖ ^ 2 ≤ K * Yc.E.form v v :=
    ⟨Yc.CE, Yc.hCE, fun v hv => Yc.hcoE v (hkE.le_domain hv)⟩
  have hcoF : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ Y.D, ‖v‖ ^ 2 ≤ K * Yc.F.form v v :=
    ⟨Yc.CF, Yc.hCF, fun v hv => Yc.hcoF v (hkF.le_domain hv)⟩
  have Edom : ∀ x, x ∈ Y.E.domain ↔ x ∈ Yc.E.domain := fun x => SetLike.ext_iff.mp hdomE x
  have Fdom : ∀ x, x ∈ Y.F.domain ↔ x ∈ Yc.F.domain := fun x => SetLike.ext_iff.mp hdomF x
  have YEF : ∀ x, x ∈ Y.E.domain ↔ x ∈ Y.F.domain := fun x => SetLike.ext_iff.mp Y.P.domain_eq x
  have YcEF : ∀ x, x ∈ Yc.E.domain ↔ x ∈ Yc.F.domain :=
    fun x => SetLike.ext_iff.mp Yc.P.domain_eq x
  have XE : ∀ x, x ∈ X.E.domain ↔ x ∈ Y.E.domain := fun x => SetLike.ext_iff.mp hXEd x
  have XF : ∀ x, x ∈ X.F.domain ↔ x ∈ Y.F.domain := fun x => SetLike.ext_iff.mp hXFd x
  have XD : ∀ x, x ∈ X.D ↔ x ∈ Y.D := fun x => SetLike.ext_iff.mp hXD x
  have YcD : ∀ x, x ∈ Yc.D ↔ x ∈ Y.D := fun x => SetLike.ext_iff.mp hDeq x
  -- the masked energy measures are those of the tied pair on the cell
  have tiedE : ∀ u ∈ Y.E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A → A ⊆ q →
      X.GammaE.measure u A = Yc.GammaE.measure u A := by
    intro u hu A hA hAq
    rw [hXEw u hu A hA, hmeasE u hu A hA (hAq.trans hqcl)]
    exact setLIntegral_congr_fun hA (fun x hx => by rw [hgw x (hAq hx)])
  have tiedF : ∀ u ∈ Y.F.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A → A ⊆ q →
      X.GammaF.measure u A = Yc.GammaF.measure u A := by
    intro u hu A hA hAq
    rw [hXFw u hu A hA, hmeasF u hu A hA (hAq.trans hqcl)]
    exact setLIntegral_congr_fun hA (fun x hx => by rw [hgw x (hAq hx)])
  -- domain memberships
  have memXb : ∀ p, (X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Y.E.domain :=
    fun p => (XE _).mp (X.P.boundary p).property
  have memXf : ∀ p, (X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Y.F.domain :=
    fun p => (XF _).mp (X.P.memF p)
  have memYb : ∀ p, (Y.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Y.E.domain :=
    fun p => (Y.P.boundary p).property
  have memYcb : ∀ p, (Yc.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Yc.E.domain :=
    fun p => (Yc.P.boundary p).property
  have memYcf : ∀ p, (Yc.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Yc.F.domain :=
    fun p => Yc.P.memF p
  -- E side: the coordinate minimizers have zero difference energy on the cell
  have hEsub : ∀ p, Yc.GammaE.measure ((X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) -
      (Yc.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ))) q = 0 := by
    intro p
    obtain ⟨U1, hU1, hrep1, hb1⟩ := hYaff p
    obtain ⟨U2, hU2, hrep2, hb2⟩ := hYcaff p
    refine aux_prop_conc_masked_measure_identification_minimizer_sub_zero hd zQ zc RQ rc hRQ hrc
      hqQ Yc.E Yc.GammaE Yc.hEc Y.D hkE hcoE (fun x => ∑ i, p i * x i)
      (Y.P.boundary p) (Yc.P.boundary p) (X.P.boundary p) (Yc.P.boundary p)
      ((Edom _).mp (memYb p)) (memYcb p) ((Edom _).mp (memXb p)) (memYcb p)
      U1 U2 hU1 hU2 hrep1 hrep2 hb1 hb2 (hXbc p) (by simpa only [sub_self] using Y.D.zero_mem)
      ?_ ?_
    · intro v hv hvD
      have hvY : v ∈ Y.E.domain := (Edom _).mpr hv
      have hvD' : v - (X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ X.D := by
        refine (XD _).mpr ?_
        have := Y.D.sub_mem hvD (hXbc p)
        simpa only [sub_sub_sub_cancel_right] using this
      have h := X.P.minE p v ((XE _).mpr hvY) hvD'
      rw [tiedE _ (memXb p) q hqmeas subset_rfl, tiedE v hvY q hqmeas subset_rfl] at h
      exact h
    · intro v hv hvD
      exact Yc.P.minE p v hv ((YcD _).mpr hvD)
  have hEb : ∀ p (A : Set (SpatialCoordinates d)), MeasurableSet A → A ⊆ q →
      X.GammaE.measure (X.P.boundary p) A = Yc.GammaE.measure (Yc.P.boundary p) A := by
    intro p A hA hAq
    rw [tiedE _ (memXb p) A hA hAq]
    exact aux_prop_conc_masked_measure_identification_eq_of_sub_zero Yc.GammaE
      ((Edom _).mp (memXb p)) (memYcb p) (hEsub p) hA hAq
  -- F side: the F-minimizers have zero difference F-energy, hence zero E-energy, on the cell
  have hFsub : ∀ p, Yc.GammaF.measure ((X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
      (Yc.P.uF p : DomainL2 (centeredCube zQ RQ hRQ))) q = 0 := by
    intro p
    obtain ⟨U1, hU1, hrep1, hb1⟩ := hYaff p
    obtain ⟨U2, hU2, hrep2, hb2⟩ := hYcaff p
    refine aux_prop_conc_masked_measure_identification_minimizer_sub_zero hd zQ zc RQ rc hRQ hrc
      hqQ Yc.F Yc.GammaF Yc.hFc Y.D hkF hcoF (fun x => ∑ i, p i * x i)
      (Y.P.boundary p) (Yc.P.boundary p) (X.P.uF p) (Yc.P.uF p)
      ((Fdom _).mp ((YEF _).mp (memYb p)))
      ((YcEF _).mp (memYcb p))
      ((Fdom _).mp (memXf p)) (memYcf p)
      U1 U2 hU1 hU2 hrep1 hrep2 hb1 hb2 (hXfc p)
      ((YcD _).mp (Yc.P.traceF p)) ?_ ?_
    · intro v hv hvD
      have hvY : v ∈ Y.F.domain := (Fdom _).mpr hv
      have hvD' : v - (X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ X.D := by
        refine (XD _).mpr ?_
        have := Y.D.sub_mem hvD (hXbc p)
        simpa only [sub_sub_sub_cancel_right] using this
      have h := X.P.minF p v ((XF _).mpr hvY) hvD'
      rw [tiedF _ (memXf p) q hqmeas subset_rfl, tiedF v hvY q hqmeas subset_rfl] at h
      exact h
    · intro v hv hvD
      exact Yc.P.minF p v hv ((YcD _).mpr hvD)
  have hEfsub : ∀ p, Yc.GammaE.measure ((X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
      (Yc.P.uF p : DomainL2 (centeredCube zQ RQ hRQ))) q = 0 := by
    intro p
    set δ : DomainL2 (centeredCube zQ RQ hRQ) :=
      (X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
        (Yc.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) with hδ
    have hdiffdom : δ ∈ Yc.E.domain :=
      Yc.E.domain.sub_mem ((Edom _).mp ((YEF _).mpr (memXf p))) ((YcEF _).mpr (memYcf p))
    have hord := energy_order_of_form_order (centeredCube zQ RQ hRQ) Yc.E Yc.F Yc.hEc Yc.hEl Yc.hFc
      Yc.hFl Yc.P.domain_eq Yc.GammaE Yc.GammaF m M hm0 Yc.horder δ hdiffdom q hqmeas
    have hF0 : (Yc.GammaF.measure δ q).toReal = 0 := by
      rw [hFsub p]; rfl
    have hE0 : (Yc.GammaE.measure δ q).toReal = 0 := by
      have h1 := hord.1
      rw [hF0] at h1
      have hn := ENNReal.toReal_nonneg (a := Yc.GammaE.measure δ q)
      nlinarith
    exact (ENNReal.toReal_eq_zero_iff _).mp hE0 |>.resolve_right
      (Yc.GammaE.measure_ne_top hdiffdom q)
  have hEf : ∀ p (A : Set (SpatialCoordinates d)), MeasurableSet A → A ⊆ q →
      X.GammaE.measure (X.P.uF p) A = Yc.GammaE.measure (Yc.P.uF p) A := by
    intro p A hA hAq
    have hXf : (X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Y.E.domain :=
      (YEF _).mpr (memXf p)
    rw [tiedE _ hXf A hA hAq]
    exact aux_prop_conc_masked_measure_identification_eq_of_sub_zero Yc.GammaE
      ((Edom _).mp hXf) ((YcEF _).mpr (memYcf p)) (hEfsub p) hA hAq
  have hQ : ∀ p, X.P.QE p = Yc.P.QE p := by
    intro p
    rw [X.P.responseE p, Yc.P.responseE p, hEb p q hqmeas subset_rfl]
  refine ⟨hQ, hEb, hEf, ?_⟩
  -- ζ: the difference of the two coordinate-minimizer differences
  intro p A hA hAq
  have hd1 : (X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
      (X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Y.E.domain :=
    Y.E.domain.sub_mem ((YEF _).mpr (memXf p)) (memXb p)
  have hd2 : (Yc.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
      (Yc.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) ∈ Yc.E.domain :=
    Yc.E.domain.sub_mem ((YcEF _).mpr (memYcf p)) (memYcb p)
  have hzero : Yc.GammaE.measure (((X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
      (X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ))) -
      ((Yc.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
        (Yc.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)))) q = 0 := by
    have hrw : ((X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
        (X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ))) -
        ((Yc.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) -
        (Yc.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ))) =
        ((X.P.uF p : DomainL2 (centeredCube zQ RQ hRQ)) - (Yc.P.uF p : DomainL2 (centeredCube zQ RQ hRQ))) -
        ((X.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ)) -
          (Yc.P.boundary p : DomainL2 (centeredCube zQ RQ hRQ))) := by abel
    rw [hrw]
    exact aux_prop_conc_masked_measure_identification_sub_zero_of_zero Yc.GammaE
      (Yc.E.domain.sub_mem ((Edom _).mp ((YEF _).mpr (memXf p))) ((YcEF _).mpr (memYcf p)))
      (Yc.E.domain.sub_mem ((Edom _).mp (memXb p)) (memYcb p)) hqmeas (hEfsub p) (hEsub p)
  rw [tiedE _ hd1 A hA hAq]
  exact aux_prop_conc_masked_measure_identification_eq_of_sub_zero Yc.GammaE
    ((Edom _).mp hd1) hd2 hzero hA hAq

end Main

/-- Identification of the canonical masked pair with a tied pair of the resampled environment.  If the
forms of `Yc` are the `exp w`-weighted forms of `Y` (`w` continuous) and both have affine trace classes,
then the canonical mask `X` of `Y` by `1_q w` has the same minimal coordinate responses as `Yc`, the same
normalized energy measures `ν` and `ζ` on every measurable subset of the cell `q`, and every ball growth
bound of `ν_Yc` transfers to `X` with the same constant. -/
theorem prop_conc_masked_measure_identification
    (d : ℕ) (hd : 2 ≤ d) (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc) (C0 m M : ℝ)
    (Y Yc : prop_conc_pair_data (centeredCube zQ RQ hRQ) zc rc hrc C0 m M)
    (hYaff : aux_prop_conc_pair_data_affine Y) (hYcaff : aux_prop_conc_pair_data_affine Yc)
    (w : SpatialCoordinates d → ℝ) (hw : Continuous w)
    (hdomE : Y.E.domain = Yc.E.domain)
    (hdiagE : ∀ u ∈ Y.E.domain, Yc.E.form u u = ∫ x, Real.exp (w x) ∂(Y.GammaE.measure u))
    (hdiagF : ∀ u ∈ Y.F.domain, Yc.F.form u u = ∫ x, Real.exp (w x) ∂(Y.GammaF.measure u))
    (hg : Measurable ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator w))
    (Kg : ℝ)
    (hKg : ∀ x, |(centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator w x| ≤ Kg)
    (X : prop_conc_pair_data (centeredCube zQ RQ hRQ) zc rc hrc C0 m M)
    (hX : X = aux_prop_conc_pair_mask_pair Y
      ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator w) hg Kg hKg) :
    (∀ p, X.P.QE p = Yc.P.QE p) ∧
    (∀ (S : Finset (Fin d → ℝ)) (A : Set (SpatialCoordinates d)), MeasurableSet A →
      A ⊆ (centeredCube zc rc hrc : Set (SpatialCoordinates d)) →
      aux_prop_conc_pair_data_nu X S A = aux_prop_conc_pair_data_nu Yc S A) ∧
    (∀ (S : Finset (Fin d → ℝ)) (A : Set (SpatialCoordinates d)), MeasurableSet A →
      A ⊆ (centeredCube zc rc hrc : Set (SpatialCoordinates d)) →
      aux_prop_conc_pair_data_zeta X S A = aux_prop_conc_pair_data_zeta Yc S A) ∧
    (∀ (S : Finset (Fin d → ℝ)) (t K : ℝ), aux_prop_conc_pair_data_growth Yc S t K →
      aux_prop_conc_pair_data_growth X S t K) := by
  classical
  subst hX
  obtain ⟨hXD, hXEd, hXFd, hXEw, hXFw, hXbc, hXfc⟩ :=
    aux_prop_conc_masked_measure_identification_mask_facts Y
      ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator w) hg Kg hKg
  obtain ⟨hQ, hEb, hEf, hEz⟩ := aux_prop_conc_masked_measure_identification_core hd zQ RQ hRQ zc rc
    hrc C0 m M Y Yc (aux_prop_conc_pair_mask_pair Y
      ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator w) hg Kg hKg)
    hYaff hYcaff w _ hw (fun x hx => Set.indicator_of_mem hx w) hdomE hdiagE hdiagF hXD hXEd hXFd
    hXEw hXFw hXbc hXfc
  have hqmeas : MeasurableSet (centeredCube zc rc hrc : Set (SpatialCoordinates d)) :=
    (centeredCube zc rc hrc).isOpen.measurableSet
  have hsum : ∑ i : Fin d, (aux_prop_conc_pair_mask_pair Y
      ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator w) hg Kg hKg).P.QE
        (Pi.single i 1) = ∑ i : Fin d, Yc.P.QE (Pi.single i 1) :=
    Finset.sum_congr rfl fun i _ => hQ _
  have hnu : ∀ (S : Finset (Fin d → ℝ)) (A : Set (SpatialCoordinates d)), MeasurableSet A →
      A ⊆ (centeredCube zc rc hrc : Set (SpatialCoordinates d)) →
      aux_prop_conc_pair_data_nu (aux_prop_conc_pair_mask_pair Y
        ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator w) hg Kg hKg) S A =
      aux_prop_conc_pair_data_nu Yc S A := by
    intro S A hA hAq
    unfold aux_prop_conc_pair_data_nu
    rw [hsum, Measure.smul_apply, Measure.smul_apply, Measure.finset_sum_apply,
      Measure.finset_sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Measure.add_apply, Measure.add_apply, hEb p A hA hAq, hEf p A hA hAq]
  refine ⟨hQ, hnu, ?_, ?_⟩
  · intro S A hA hAq
    unfold aux_prop_conc_pair_data_zeta
    rw [hsum, Measure.smul_apply, Measure.smul_apply, Measure.finset_sum_apply,
      Measure.finset_sum_apply]
    congr 1
    exact Finset.sum_congr rfl fun p _ => hEz p A hA hAq
  · intro S t K hgrowth x ρ hρ hρr
    have hball : MeasurableSet (Metric.ball x ρ ∩
        (centeredCube zc rc hrc : Set (SpatialCoordinates d))) :=
      Metric.isOpen_ball.measurableSet.inter hqmeas
    rw [hnu S _ hball Set.inter_subset_right]
    exact hgrowth x ρ hρ hρr

end
end Paper
