module

public import SubdiffusiveProcess.Paper.prop_conc_weighted_identification_bridge
public import SubdiffusiveProcess.Paper.prop_conc_controlled_weighted_convergence
public import SubdiffusiveProcess.Paper.prop_conc_weighted_measure_identification
public import SubdiffusiveProcess.Paper.prop_conc_core_measure_data
public import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
public import SubdiffusiveProcess.Paper.lem_replace
public import SubdiffusiveProcess.DirichletForm.KilledDomainOrder

@[expose] public section

/-! Deterministic side identification.  A form `E` with energy measure, the operator limit `G` of
cutoff Green operators `a` and the operator limit `Gp` of the Green operators of a coefficient
sequence `b = exp g * a` are supplied together with a form `E'` of `Gp` whose energy measure has the
boundary-glb property at one slope.  The weighted killed-class infimum of `E` in the same affine trace
class is then that boundary glb.  Nothing probabilistic is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Comparable forms on one domain share their killed domains. -/
theorem aux_prop_conc_weighted_identification_side_killed_transfer
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}
    (E F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm mu) (hdom : E.domain = F.domain)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hform : ∀ v ∈ E.domain, c * E.form v v ≤ F.form v v ∧ F.form v v ≤ C * E.form v v)
    (U : Set X) (D : Submodule ℝ (Lp ℝ 2 mu)) (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D) :
    _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain F U D := by
  have h1 := _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain.eq_of_isKilledDomain hD
    (_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure E U)
  rw [h1, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.killedCoreClosure_eq_of_form_bounds E F hdom c C hc hC hform U]
  exact _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure F U

/-- A bounded measurable density compares the integral against a finite measure with its total mass. -/
theorem aux_prop_conc_weighted_identification_side_integral_bounds
    {X : Type*} [MeasurableSpace X] (nu : Measure X) [IsFiniteMeasure nu]
    (f : X → ℝ) (hf : Measurable f) (lo hi : ℝ) (hlo : ∀ x, lo ≤ f x) (hhi : ∀ x, f x ≤ hi) :
    lo * (nu Set.univ).toReal ≤ ∫ x, f x ∂nu ∧ ∫ x, f x ∂nu ≤ hi * (nu Set.univ).toReal := by
  have hint : Integrable f nu := by
    refine Integrable.mono' (integrable_const (max |lo| |hi|)) hf.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by
      have := neg_abs_le lo
      have := le_max_left |lo| |hi|
      linarith only [hlo x, this, ‹-|lo| ≤ lo›], by
      have := le_abs_self hi
      have := le_max_right |lo| |hi|
      linarith only [hhi x, this, ‹hi ≤ |hi|›]⟩
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

/-- The weighted killed-class infimum of `E` in the trace class of `up` is the boundary glb of the
weighted limit form at the resampled configuration. -/
theorem prop_conc_weighted_identification_side
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (S : ResponseSpace (centeredCube zQ R hR))
    (hS : S.space = killedSobolevGraph (centeredCube zQ R hR))
    (a b : ℕ → PositiveCoefficient (centeredCube zQ R hR))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd zQ R hR S a)
    (GN FN : ℕ → DomainL2 (centeredCube zQ R hR) →L[ℝ] DomainL2 (centeredCube zQ R hR))
    (G Gp : DomainL2 (centeredCube zQ R hR) →L[ℝ] DomainL2 (centeredCube zQ R hR))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hFN : ∀ n f, FN n f =
      (responseSolution S (b n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConvG : Tendsto GN atTop (𝓝 G)) (hConvGp : Tendsto FN atTop (𝓝 Gp))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (hEloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm)
    (D : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) D)
    (g : SpatialCoordinates d → ℝ) (hg : Continuous g)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict
        (centeredCube zQ R hR : Set (SpatialCoordinates d))]
      fun x => Real.exp (g x) * (a n).val x)
    (E' : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma' : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E'.toClosedForm)
    (hE' : ∀ u, E'.energy u = limitFormEnergy Gp u)
    (hcore' : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E'.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (up : DomainL2 (centeredCube zQ R hR)) (hup : up ∈ E.domain)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑up =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U)
    (bv : SpatialCoordinates d → ℝ)
    (hUb : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), U x = bv x)
    (Lam : ℝ)
    (hLam : IsGLB (aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) E'.toClosedForm Gamma'
      (centeredCube zq r hr : Set (SpatialCoordinates d)) bv) Lam) :
    sInf {e : ℝ | ∃ v ∈ E.domain, v - up ∈ D ∧
      e = (∫⁻ x in (centeredCube zq r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v)).toReal} = Lam := by
  classical
  let Q := centeredCube zQ R hR
  have hQmeas : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  have hcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) :=
    lane2_isCompact_closure_centeredCube zQ hR
  obtain ⟨C0, hC0⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  set K : ℝ := max C0 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  let gt : SpatialCoordinates d → ℝ := fun x => max (-K) (min K (g x))
  have hgt_meas : Measurable gt :=
    (continuous_const.max (continuous_const.min hg)).measurable
  have hgt_bound : ∀ x, |gt x| ≤ K := by
    intro x
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith only [hK0]) (min_le_left _ _)⟩
  have hgt_eq : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), gt x = g x := by
    intro x hx
    have hx1 : ‖g x‖ ≤ K := (hC0 x hx).trans (le_max_left _ _)
    have hx2 := abs_le.mp (by simpa only [Real.norm_eq_abs] using hx1)
    show max (-K) (min K (g x)) = g x
    rw [min_eq_right hx2.2, max_eq_right hx2.1]
  -- weighted convergence at the represented configuration
  obtain ⟨FN', F, EF, hFN', hFconv, _hFsym, _hFpos, hFE, hdomEF, hcoreEF, hdiagEF⟩ :=
    prop_conc_controlled_weighted_convergence hd zQ R hR S hS a b A GN G hGN hConvG E hE hcore
      Gamma (fun x => Real.exp (g x))
      (Real.continuous_exp.comp hg).continuousOn (fun x _ => Real.exp_pos _) hweight
  have hFNeq : FN' = FN := by
    funext n
    apply ContinuousLinearMap.ext
    intro f
    rw [hFN' n f, hFN n f]
  have hFGp : F = Gp := by
    rw [hFNeq] at hFconv
    exact tendsto_nhds_unique hFconv hConvGp
  subst hFGp
  -- identification of the domains and diagonal forms of E' and EF
  have hdomE' : E.domain = E'.domain := by
    apply SetLike.coe_injective
    have h1 := aux_thm_prop_domain_eq_of_energy EF.toClosedForm F hFE
    have h2 := aux_thm_prop_domain_eq_of_energy E'.toClosedForm F hE'
    rw [hdomEF]
    exact h1.trans h2.symm
  have hformE' : ∀ u ∈ E.domain, E'.form u u = ∫ x, Real.exp (gt x) ∂(Gamma.measure u) := by
    intro u hu
    have huEF : u ∈ EF.domain := hdomEF ▸ hu
    have huE' : u ∈ E'.domain := hdomE' ▸ hu
    have h1 := aux_thm_prop_form_eq_toReal_energy E'.toClosedForm F hE' u huE'
    have h2 := aux_thm_prop_form_eq_toReal_energy EF.toClosedForm F hFE u huEF
    rw [h1, ← h2, hdiagEF u hu]
    obtain ⟨Cc, hCc⟩ := hcore
    have hsupp : Gamma.measure u (Q : Set (SpatialCoordinates d))ᶜ = 0 :=
      aux_prop_conc_core_measure_data_energy_measure_support Gamma hQmeas hCc hu
    have hmem : ∀ᵐ x ∂Gamma.measure u, x ∈ (Q : Set (SpatialCoordinates d)) :=
      ae_iff.mpr hsupp
    apply integral_congr_ae
    filter_upwards [hmem] with x hx
    rw [hgt_eq x (subset_closure hx)]
  -- weighted energy measure of E'
  have hmeasE' := (prop_conc_weighted_measure_identification Q E E' Gamma Gamma' hcore hcore'
    hEloc hdomE' gt hgt_meas K hgt_bound hformE').1
  -- comparability of the two forms and transfer of the killed domain
  have hcompare : ∀ v ∈ E.domain, Real.exp (-K) * E.form v v ≤ E'.form v v ∧
      E'.form v v ≤ Real.exp K * E.form v v := by
    intro v hv
    let : IsFiniteMeasure (Gamma.measure v) := ⟨Gamma.measure_univ_lt_top v hv⟩
    have hb := aux_prop_conc_weighted_identification_side_integral_bounds (Gamma.measure v)
      (fun x => Real.exp (gt x)) (Real.measurable_exp.comp hgt_meas) (Real.exp (-K)) (Real.exp K)
      (fun x => Real.exp_le_exp.mpr (abs_le.mp (hgt_bound x)).1)
      (fun x => Real.exp_le_exp.mpr (abs_le.mp (hgt_bound x)).2)
    rw [Gamma.measure_univ v hv] at hb
    rw [hformE' v hv]
    exact hb
  have hDE' := aux_prop_conc_weighted_identification_side_killed_transfer E.toClosedForm
    E'.toClosedForm hdomE' (Real.exp (-K)) (Real.exp K) (Real.exp_pos _) (Real.exp_pos _).le
    hcompare _ D hD
  have hcoerc : ∃ K' : ℝ, 0 < K' ∧ ∀ v ∈ D, ‖v‖ ^ 2 ≤ K' * E'.form v v := by
    obtain ⟨K', hK', hbound⟩ := aux_lem_replace_limit_form_coercivity F E'.toClosedForm
      ((aux_thm_prop_domain_eq_of_energy E'.toClosedForm F hE'))
      (fun u hu => aux_thm_prop_form_eq_toReal_energy E'.toClosedForm F hE' u hu)
    exact ⟨K', hK', fun v hv => hbound v (hDE'.le_domain hv)⟩
  have hupE' : up ∈ E'.domain := hdomE' ▸ hup
  have hleast := prop_conc_weighted_identification_bridge d hd zQ zq R r hR hr hqQ E' Gamma' hcore'
    D hDE' hcoerc up hupE' U hU hurep bv hUb Lam hLam
  -- rewrite the killed-class set as the least-value set
  have hset : {e : ℝ | ∃ v ∈ E.domain, v - up ∈ D ∧
      e = (∫⁻ x in (centeredCube zq r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v)).toReal} =
      {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ D ∧
        t = (Gamma'.measure (up + w)
          (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal} := by
    have hval : ∀ v ∈ E.domain, (Gamma'.measure v
        (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal =
        (∫⁻ x in (centeredCube zq r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v)).toReal := by
      intro v hv
      rw [hmeasE' v hv _ (centeredCube zq r hr).isOpen.measurableSet]
      congr 1
      apply setLIntegral_congr_fun (centeredCube zq r hr).isOpen.measurableSet
      intro x hx
      show ENNReal.ofReal (Real.exp (gt x)) = ENNReal.ofReal (Real.exp (g x))
      rw [hgt_eq x (subset_closure (hqQ hx))]
    ext e
    constructor
    · rintro ⟨v, hv, hvD, rfl⟩
      refine ⟨v - up, hvD, ?_⟩
      rw [show up + (v - up) = v by abel, hval v hv]
    · rintro ⟨w, hw, rfl⟩
      have hvE : up + w ∈ E.domain := E.domain.add_mem hup (hD.le_domain hw)
      refine ⟨up + w, hvE, by simpa only [add_sub_cancel_left] using hw, ?_⟩
      rw [hval _ hvE]
  rw [hset]
  exact hleast.csInf_eq

end
end SubdiffusiveProcess.Paper
