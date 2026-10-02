import SubdiffusiveProcess.Paper.prop_conc_boundary_truncation
import SubdiffusiveProcess.Paper.prop_conc_local_minimizer_variations
import SubdiffusiveProcess.Paper.prop_boundary
import SubdiffusiveProcess.DirichletForm.KilledDomainOrder
import SubdiffusiveProcess.DirichletForm.LocalMinimum

/-! Put two actual local affine minimizers into one killed-domain trace class.
Only the representative outside the observation cell is adjusted; both local energy measures are preserved. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- Comparable local minimizers have representatives in one trace class with unchanged cell measures. -/
theorem prop_conc_common_trace_minimizers
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (E F : _root_.DirichletForm (volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain) (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (horder : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v ∧ F.form v v ≤ M * E.form v v)
    (p : Fin d → ℝ) (LE LF KE KF t : ℝ)
    (uE : DirichletForm.LocalAffineMinimizer z r hr h3r E GammaE p LE KE t)
    (uF : DirichletForm.LocalAffineMinimizer z r hr h3r F GammaF p LF KF t) :
    ∃ vF : DomainL2 (centeredCube z (3 * r) h3r),
      vF ∈ F.domain ∧
      vF - uE.u ∈ E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (GammaE.measure vF).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) =
        (GammaE.measure uF.u).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (GammaF.measure vF).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) =
        (GammaF.measure uF.u).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      ∀ v ∈ F.domain,
        v - uE.u ∈ E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)) →
        (GammaF.measure vF (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (GammaF.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  let q : Set (SpatialCoordinates d) := centeredCube z r hr
  let D := E.toClosedForm.killedCoreClosure q
  let w : DomainL2 (centeredCube z (3 * r) h3r) := uF.u - uE.u
  let wc : SpatialCoordinates d → ℝ := fun x => uF.representative x - uE.representative x
  have hw : w ∈ E.domain := E.domain.sub_mem (hdom.symm ▸ uF.mem) uE.mem
  have hwrep : (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] wc := by
    filter_upwards [Lp.coeFn_sub uF.u uE.u, uF.coeFn, uE.coeFn] with x hx hf he
    exact hx.trans (by rw [Pi.sub_apply, hf, he])
  have hwc : ContinuousOn wc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) :=
    uF.continuous.sub uE.continuous
  have hwb : ∀ x ∈ frontier q, wc x = 0 := by
    intro x hx
    change uF.representative x - uE.representative x = 0
    rw [uF.boundary x hx, uE.boundary x hx, sub_self]
  obtain ⟨wq, hwq⟩ := aux_prop_boundary_indicator_toLp (closure q) isClosed_closure.measurableSet w wc hwrep
  have hqQ : q ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith only [hr])
  have hwD : wq ∈ D := (prop_conc_boundary_truncation d hd z z (3 * r) r h3r hr hqQ
    E GammaE hEcore D (DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _)
    w hw wc hwc hwrep hwb wq hwq).1
  let vF : DomainL2 (centeredCube z (3 * r) h3r) := uE.u + wq
  have hvE : vF ∈ E.domain := E.domain.add_mem uE.mem hwD.1
  have hvF : vF ∈ F.domain := hdom ▸ hvE
  have htrace : vF - uE.u ∈ D := by
    simpa only [vF, add_sub_cancel_left] using hwD
  have heq : (uF.u : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).restrict q]
      (vF : SpatialCoordinates d → ℝ) :=
    aux_prop_boundary_ae_eq_add_on q (centeredCube z r hr).isOpen.measurableSet
      uE.u uF.u wq uE.representative uF.representative uE.coeFn uF.coeFn hwq
  have hDEq := DirichletForm.ClosedForm.killedCoreClosure_eq_of_form_bounds E.toClosedForm
    F.toClosedForm hdom m M hm hM horder q
  refine ⟨vF, hvF, htrace,
    (GammaE.locality uF.u (hdom.symm ▸ uF.mem) vF hvE q (centeredCube z r hr).isOpen heq).symm,
    (GammaF.locality uF.u uF.mem vF hvF q (centeredCube z r hr).isOpen heq).symm, ?_⟩
  intro v hv htr
  have hdif : v - vF ∈ F.toClosedForm.killedCoreClosure q := by
    rw [← hDEq]
    have h := D.sub_mem htr htrace
    simpa only [sub_sub_sub_cancel_right] using h
  exact GammaF.local_minimum_of_ae_eq q (centeredCube z r hr).isOpen
    (F.toClosedForm.killedCoreClosure q)
    (DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _).le_domain
    uF.u vF uF.mem hvF heq (prop_conc_local_minimizer_variations z r hr h3r F GammaF p LF KF t uF)
    v hv hdif

end
end Paper
