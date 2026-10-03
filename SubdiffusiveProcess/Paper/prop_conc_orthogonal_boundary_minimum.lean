module

public import SubdiffusiveProcess.Paper.prop_conc_boundary_truncation
public import SubdiffusiveProcess.Paper.prop_conc_local_minimizer_variations
public import SubdiffusiveProcess.Paper.prop_conc_local_affine_order
public import SubdiffusiveProcess.DirichletForm.LocalEnergyQuadratic

@[expose] public section

/-! A continuous local orthogonal representative realizes the approved one-cell boundary minimum.
Only the energy measure on the observation cube enters the conclusion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- Orthogonality and the prescribed continuous trace identify the local boundary minimum. -/
theorem prop_conc_orthogonal_boundary_minimum
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (E : _root_.DirichletForm (volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (u : DomainL2 (centeredCube z (3 * r) h3r)) (hu : u ∈ E.domain)
    (uc b : SpatialCoordinates d → ℝ)
    (hc : ContinuousOn uc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hrep : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] uc)
    (hb : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), uc x = b x)
    (hortho : ∀ v ∈ E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)),
      E.form u v = 0) :
    IsLeast (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm Gamma
      (centeredCube z r hr : Set (SpatialCoordinates d)) b)
      (Gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  let q : Set (SpatialCoordinates d) := centeredCube z r hr
  let D := E.toClosedForm.killedCoreClosure q
  have hD := DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure E.toClosedForm q
  refine ⟨⟨u, uc, hu, hc, hrep, hb, rfl⟩, ?_⟩
  rintro e ⟨v, vc, hv, hvc, hvrep, hvb, rfl⟩
  let w := v - u
  let wc : SpatialCoordinates d → ℝ := fun x => vc x - uc x
  have hw : w ∈ E.domain := E.domain.sub_mem hv hu
  have hwrep : (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] wc := by
    filter_upwards [Lp.coeFn_sub v u, hvrep, hrep] with x hx hvx hux
    exact hx.trans (by rw [Pi.sub_apply, hvx, hux])
  have hwc : ContinuousOn wc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) := hvc.sub hc
  have hwb : ∀ x ∈ frontier q, wc x = 0 := by
    intro x hx
    change vc x - uc x = 0
    rw [hvb x hx, hb x hx, sub_self]
  obtain ⟨wq, hwq⟩ := aux_prop_boundary_indicator_toLp (closure q) isClosed_closure.measurableSet w wc hwrep
  have hqQ : q ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith only [hr])
  have hwD : wq ∈ D := (prop_conc_boundary_truncation d hd z z (3 * r) r h3r hr hqQ
    E Gamma hcore D hD w hw wc hwc hwrep hwb wq hwq).1
  have huw : u + wq ∈ E.domain := E.domain.add_mem hu (hD.le_domain hwD)
  have heq : (v : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).restrict q]
      ((u + wq : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ) :=
    aux_prop_boundary_ae_eq_add_on q (centeredCube z r hr).isOpen.measurableSet
      u v wq uc vc hrep hvrep hwq
  have hGamma := congrArg (fun nu => nu Set.univ)
    (Gamma.locality v hv (u + wq) huw q (centeredCube z r hr).isOpen heq)
  simp only [Measure.restrict_apply_univ] at hGamma
  rw [hGamma]
  apply Gamma.local_minimum_of_cross_eq_zero q (centeredCube z r hr).isOpen.measurableSet
    D hD.le_domain u hu _ (u + wq) huw (by simpa only [add_sub_cancel_left] using hwD)
  intro t ht
  rw [aux_prop_conc_local_minimizer_variations_cross E.toClosedForm Gamma q
    (centeredCube z r hr).isOpen D hD u t hu ht]
  exact hortho t ht

end
end Paper
