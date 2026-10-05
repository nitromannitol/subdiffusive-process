module

public import SubdiffusiveProcess.Paper.prop_conc_common_trace_minimizers

@[expose] public section

/-! Common-trace gluing for arbitrary continuous local representatives.
This extends the checked coordinate gluing interface to all affine slopes without new growth premises. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Continuous local minimizers with the same boundary values admit common-trace representatives. -/
theorem prop_conc_common_trace_representatives
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (E F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (hEcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain) (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (horder : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v ∧ F.form v v ≤ M * E.form v v)
    (uE uF : DomainL2 (centeredCube z (3 * r) h3r)) (huE : uE ∈ E.domain) (huF : uF ∈ F.domain)
    (ucE ucF b : SpatialCoordinates d → ℝ)
    (hcE : ContinuousOn ucE (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hcF : ContinuousOn ucF (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hrepE : (uE : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] ucE)
    (hrepF : (uF : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] ucF)
    (hbE : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), ucE x = b x)
    (hbF : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), ucF x = b x)
    (hminF : ∀ v ∈ F.domain,
      v - uF ∈ F.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)) →
      (GammaF.measure uF (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaF.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) :
    ∃ vF : DomainL2 (centeredCube z (3 * r) h3r),
      vF ∈ F.domain ∧
      vF - uE ∈ E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (GammaE.measure vF).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) =
        (GammaE.measure uF).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (GammaF.measure vF).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) =
        (GammaF.measure uF).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      ∀ v ∈ F.domain,
        v - uE ∈ E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)) →
        (GammaF.measure vF (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (GammaF.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  let q : Set (SpatialCoordinates d) := centeredCube z r hr
  let D := E.toClosedForm.killedCoreClosure q
  let w : DomainL2 (centeredCube z (3 * r) h3r) := uF - uE
  let wc : SpatialCoordinates d → ℝ := fun x => ucF x - ucE x
  have hw : w ∈ E.domain := E.domain.sub_mem (hdom.symm ▸ huF) huE
  have hwrep : (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] wc := by
    filter_upwards [Lp.coeFn_sub uF uE, hrepF, hrepE] with x hx hf he
    exact hx.trans (by rw [Pi.sub_apply, hf, he])
  have hwc : ContinuousOn wc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) :=
    hcF.sub hcE
  have hwb : ∀ x ∈ frontier q, wc x = 0 := by
    intro x hx
    change ucF x - ucE x = 0
    rw [hbF x hx, hbE x hx, sub_self]
  obtain ⟨wq, hwq⟩ := aux_prop_boundary_indicator_toLp (closure q) isClosed_closure.measurableSet w wc hwrep
  have hqQ : q ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith only [hr])
  have hwD : wq ∈ D := (prop_conc_boundary_truncation d hd z z (3 * r) r h3r hr hqQ
    E GammaE hEcore D (_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _)
    w hw wc hwc hwrep hwb wq hwq).1
  let vF : DomainL2 (centeredCube z (3 * r) h3r) := uE + wq
  have hvE : vF ∈ E.domain := E.domain.add_mem huE hwD.1
  have hvF : vF ∈ F.domain := hdom ▸ hvE
  have htrace : vF - uE ∈ D := by
    simpa only [vF, add_sub_cancel_left] using hwD
  have heq : (uF : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).restrict q]
      (vF : SpatialCoordinates d → ℝ) :=
    aux_prop_boundary_ae_eq_add_on q (centeredCube z r hr).isOpen.measurableSet
      uE uF wq ucE ucF hrepE hrepF hwq
  have hDEq := _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.killedCoreClosure_eq_of_form_bounds E.toClosedForm
    F.toClosedForm hdom m M hm hM horder q
  refine ⟨vF, hvF, htrace,
    (GammaE.locality uF (hdom.symm ▸ huF) vF hvE q (centeredCube z r hr).isOpen heq).symm,
    (GammaF.locality uF huF vF hvF q (centeredCube z r hr).isOpen heq).symm, ?_⟩
  intro v hv htr
  have hdif : v - vF ∈ F.toClosedForm.killedCoreClosure q := by
    rw [← hDEq]
    have h := D.sub_mem htr htrace
    simpa only [sub_sub_sub_cancel_right] using h
  exact GammaF.local_minimum_of_ae_eq q (centeredCube z r hr).isOpen
    (F.toClosedForm.killedCoreClosure q)
    (_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _).le_domain
    uF vF huF hvF heq hminF
    v hv hdif

end
end SubdiffusiveProcess.Paper
