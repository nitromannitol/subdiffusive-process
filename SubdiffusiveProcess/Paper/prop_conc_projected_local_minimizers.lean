import SubdiffusiveProcess.Paper.inputs_classical_closed_form_projection
import SubdiffusiveProcess.Paper.prop_conc_local_minimizer_variations
import SubdiffusiveProcess.DirichletForm.AffineProjection
import SubdiffusiveProcess.DirichletForm.LocalEnergyQuadratic



set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
namespace Paper
noncomputable section

/-- Coercivity and a killed-domain trace family produce local minimizers for every slope at once. -/
theorem prop_conc_projected_local_minimizers
    {X V : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [AddCommGroup V] [Module ℝ V] {mu : Measure X}
    (E : DirichletForm.ClosedForm mu) (Gamma : DirichletForm.EnergyMeasure E)
    (A : Set X) (hA : IsOpen A) (D : Submodule ℝ (Lp ℝ 2 mu))
    (hD : DirichletForm.IsKilledDomain E A D)
    (C : ℝ) (hC : 0 < C) (hcoerc : ∀ v ∈ E.domain, ‖v‖ ^ 2 ≤ C * E.form v v)
    (b : V →ₗ[ℝ] E.domain) :
    ∃ (u : V →ₗ[ℝ] Lp ℝ 2 mu) (Q : QuadraticForm ℝ V),
      (∀ p, u p ∈ E.domain) ∧ (∀ p, u p - (b p : Lp ℝ 2 mu) ∈ D) ∧
      (∀ p, ∀ w ∈ D, E.form (u p) w = 0) ∧
      (∀ p, ∀ v ∈ E.domain, v - (b p : Lp ℝ 2 mu) ∈ D →
        (Gamma.measure (u p) A).toReal ≤ (Gamma.measure v A).toReal) ∧
      ∀ p, Q p = (Gamma.measure (u p) A).toReal := by
  have hex : ∀ v ∈ E.domain, ∃! u, E.IsAffineProjection D v u := fun v hv =>
    inputs_classical_closed_form_projection E D hD.le_domain hD.isClosed C hC hcoerc v hv
  let u : V →ₗ[ℝ] Lp ℝ 2 mu := (E.affineProjection D hD.le_domain hex).comp b
  have hu (p : V) : E.IsAffineProjection D (b p) (u p) :=
    E.affineProjection_spec D hD.le_domain hex (b p)
  refine ⟨u, Gamma.localQuadratic u (fun p => (hu p).1) A,
    (fun p => (hu p).1), (fun p => (hu p).2.1), (fun p => (hu p).2.2), ?_,
    Gamma.localQuadratic_apply u (fun p => (hu p).1) A hA.measurableSet⟩
  intro p v hv htrace
  have hdiff : v - u p ∈ D := by
    have h := D.sub_mem htrace (hu p).2.1
    simpa only [sub_sub_sub_cancel_right] using h
  apply Gamma.local_minimum_of_cross_eq_zero A hA.measurableSet D hD.le_domain
    (u p) (hu p).1 _ v hv hdiff
  intro w hw
  rw [aux_prop_conc_local_minimizer_variations_cross E Gamma A hA D hD
    (u p) w (hu p).1 hw]
  exact (hu p).2.2 w hw

end
end Paper
