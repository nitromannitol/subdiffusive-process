import SubdiffusiveProcess.AuditRepairs.ZeroInverseConstruction
import SubdiffusiveProcess.Paper.lem_borel_weights
import SubdiffusiveProcess.Paper.prop_conc_masked_form_data








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.AuditRepairs
open Paper

/-- The weighted inverse and its dual identification are constructed, with no weighted
inverse, weighted convergence or weighted variational hypothesis. -/
theorem weighted_inverse_exists
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (Gbase : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hbase : ∀ u, E.toClosedForm.energy u = limitFormEnergy Gbase u)
    (hcore : ∃ C : Set (DomainL2 Q),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (hsupp : ∀ u ∈ E.toClosedForm.domain,
      Gamma.measure u (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (ell : SpatialCoordinates d → ℝ)
    (hell : ContinuousOn ell (closure (Q : Set (SpatialCoordinates d))) ∧
      ∃ K : ℝ, ∀ x ∈ (Q : Set (SpatialCoordinates d)), |ell x| ≤ K) :
    ∃ (Ed : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (Gammad : DirichletForm.EnergyMeasure Ed.toClosedForm)
      (G : DomainL2 Q →L[ℝ] DomainL2 Q),
      Ed.domain = E.domain ∧
      DirichletForm.IsResolvent Ed.toClosedForm 0 G ∧
      (∀ f g : DomainL2 Q, inner ℝ f (G g) = inner ℝ (G f) g) ∧
      Function.Injective G ∧
      (∀ f : DomainL2 Q, IsLUB {t : ℝ | ∃ u : DomainL2 Q,
        u ∈ E.domain ∧ t = 2 * inner ℝ f u -
          ∫ x in (Q : Set (SpatialCoordinates d)), Real.exp (-ell x) ∂(Gamma.measure u)}
        (inner ℝ f (G f))) ∧
      (∀ u : DomainL2 Q, Ed.energy u = limitFormEnergy G u) ∧
      (∀ u ∈ E.domain, ∀ v ∈ E.domain,
        Ed.form u v = DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
          (fun x => Real.exp (-ell x))) ∧
      DirichletForm.IsRegular Ed.toClosedForm ∧
      DirichletForm.IsStronglyLocal Ed.toClosedForm ∧
      (∀ u ∈ E.domain, ∀ v ∈ E.domain,
        ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
          Gammad.cross u v B = DirichletForm.signedIntegralOn (Gamma.cross u v) B
            (fun x => Real.exp (-ell x))) ∧
      (∀ u ∈ E.domain, Ed.form u u =
        ∫ x in (Q : Set (SpatialCoordinates d)), Real.exp (-ell x) ∂Gamma.measure u) := by
  classical
  obtain ⟨hcont, K, hK⟩ := hell
  set gom : SpatialCoordinates d → ℝ :=
    (Q : Set (SpatialCoordinates d)).piecewise (fun x => -ell x) (fun _ => 0) with hgomdef
  have hQmeas : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  have hgmeas : Measurable gom :=
    ContinuousOn.measurable_piecewise (hcont.mono subset_closure).neg continuousOn_const hQmeas
  have hgbdd : ∀ x, |gom x| ≤ |K| := by
    intro x
    by_cases hx : x ∈ (Q : Set (SpatialCoordinates d))
    · rw [hgomdef, piecewise_eq_of_mem _ _ _ hx, abs_neg]
      exact (hK x hx).trans (le_abs_self K)
    · rw [hgomdef, piecewise_eq_of_notMem _ _ _ hx, abs_zero]
      exact abs_nonneg K
  have hgQ : ∀ x ∈ (Q : Set (SpatialCoordinates d)), gom x = -ell x := fun x hx => by
    rw [hgomdef, piecewise_eq_of_mem _ _ _ hx]
  have hC : 0 < ‖Gbase‖ + 1 := by positivity
  have hcoerc : ∀ u ∈ E.domain, ‖u‖ ^ 2 ≤ (‖Gbase‖ + 1) * E.form u u := by
    intro u hu
    exact norm_sq_le_form_of_dual_energy E.toClosedForm Gbase hbase u hu
  obtain ⟨D⟩ := prop_conc_masked_form_data Q E Gamma hcore hloc
    gom hgmeas |K| hgbdd (‖Gbase‖ + 1) hC hcoerc
  obtain ⟨G, hG⟩ := exists_zero_resolvent D.form.toClosedForm
    (Real.exp |K| * (‖Gbase‖ + 1)) (mul_pos (Real.exp_pos _) hC) D.coercive
  have hswap : ∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ B : Set (SpatialCoordinates d),
      DirichletForm.signedIntegralOn (Gamma.cross u v) B (fun x => Real.exp (gom x)) =
        DirichletForm.signedIntegralOn (Gamma.cross u v) B (fun x => Real.exp (-ell x)) := by
    intro u hu v hv B
    refine aux_lem_borel_weights_signedIntegralOn_congr_off _ _ hQmeas.compl ?_ _ _ ?_ B
    · intro A hA hAQ
      have hu0 : Gamma.measure u A = 0 := measure_mono_null hAQ (hsupp u hu)
      have hv0 : Gamma.measure v A = 0 := measure_mono_null hAQ (hsupp v hv)
      have h := Gamma.abs_cross_le u hu v hv A hA
      rw [hu0, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at h
      exact abs_nonpos_iff.mp h
    · intro x hx
      rw [hgQ x (not_not.mp hx)]
  have hdiag : ∀ u ∈ E.domain, D.form.form u u =
      ∫ x in (Q : Set (SpatialCoordinates d)), Real.exp (-ell x) ∂(Gamma.measure u) := by
    intro u hu
    have hae : ∀ᵐ x ∂Gamma.measure u, x ∈ (Q : Set (SpatialCoordinates d)) :=
      ae_iff.mpr (hsupp u hu)
    rw [D.diagonal u hu]
    have hrestrict : Gamma.measure u = (Gamma.measure u).restrict
        (Q : Set (SpatialCoordinates d)) :=
      (Measure.restrict_eq_self_of_ae_mem hae).symm
    conv_lhs => rw [hrestrict]
    exact setIntegral_congr_fun hQmeas fun x hx => by rw [hgQ x hx]
  have hLUB : ∀ f : DomainL2 Q, IsLUB {t : ℝ | ∃ u : DomainL2 Q,
      u ∈ E.domain ∧ t = 2 * inner ℝ f u -
        ∫ x in (Q : Set (SpatialCoordinates d)), Real.exp (-ell x) ∂(Gamma.measure u)}
      (inner ℝ f (G f)) := by
    intro f
    have hsets : {t : ℝ | ∃ u : DomainL2 Q, u ∈ D.form.domain ∧
        t = 2 * inner ℝ f u - D.form.form u u} =
        {t : ℝ | ∃ u : DomainL2 Q, u ∈ E.domain ∧
          t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
            Real.exp (-ell x) ∂(Gamma.measure u)} := by
      ext t
      simp only [mem_setOf_eq, D.domain_eq]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by rw [hdiag u hu]⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by rw [hdiag u hu]⟩
    rw [← hsets]
    exact zero_resolvent_isLUB hG f
  refine ⟨D.form, D.Gamma, G, D.domain_eq, hG, ?_, zero_resolvent_injective hG,
    hLUB, ?_, ?_, ?_, D.locality, ?_, hdiag⟩
  · intro f g
    rw [hG.inner_comm f g, real_inner_comm]
  · intro u
    exact aux_lem_borel_weights_energy_eq_dual D.form.toClosedForm G
      (zero_resolvent_isLUB hG) u
  · intro u hu v hv
    rw [← (D.Gamma.cross_univ u (D.domain_eq.symm ▸ hu) v (D.domain_eq.symm ▸ hv)),
      D.cross u hu v hv Set.univ MeasurableSet.univ]
    exact hswap u hu v hv Set.univ
  · exact aux_prop_conc_core_measure_data_isRegular_of_core Q D.form.toClosedForm D.core
  · intro u hu v hv B hB
    rw [D.cross u hu v hv B hB, hswap u hu v hv B]

end SubdiffusiveProcess.AuditRepairs
