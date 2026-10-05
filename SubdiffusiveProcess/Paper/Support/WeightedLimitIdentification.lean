module

public import SubdiffusiveProcess.WeightedLimitIdentification.EqualBaseEnergyMeasures
public import SubdiffusiveProcess.WeightedLimitIdentification.ZeroInverseConstruction
public import SubdiffusiveProcess.Paper.prop_21_dual_energy_operator_unique

@[expose] public section








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.WeightedLimitIdentification

/-- Once the unweighted energies agree, the weighted cluster is the constructed
original-form inverse. The weighted energy and domain inputs are conclusions of
the deterministic continuous-weight proposition, consumed only in this application. -/
theorem weighted_operator_eq_of_base_identification
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (ΓE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (ΓF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (hcore : ∃ C : Set (DomainL2 Q),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hbase : ∀ u, E.energy u = F.energy u)
    (rho : SpatialCoordinates d → ℝ)
    (D W : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gdeleted Grho : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hDdom : D.domain = E.domain)
    (hDdiag : ∀ u ∈ E.domain,
      D.form u u = ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂ΓE.measure u)
    (hDenergy : ∀ u, D.energy u = limitFormEnergy Gdeleted u)
    (hDresolvent : _root_.SubdiffusiveProcess.DirichletForm.IsResolvent D.toClosedForm 0 Gdeleted)
    (hWdom : W.domain = F.domain)
    (hWdiag : ∀ u ∈ F.domain,
      W.energy u = (((∫ x in (Q : Set (SpatialCoordinates d)),
        rho x ∂ΓF.measure u) : ℝ) : EReal))
    (hWenergy : ∀ u, W.energy u = limitFormEnergy Grho u)
    (hGrhosym : ∀ f g : DomainL2 Q, inner ℝ (Grho f) g = inner ℝ f (Grho g))
    (hGrhopos : ∀ f : DomainL2 Q, 0 ≤ inner ℝ f (Grho f)) : Grho = Gdeleted := by
  have hdom : E.domain = F.domain := by
    ext u
    exact _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.mem_domain_iff_of_energy_eq hbase u
  have hWDdom : W.domain = D.domain := hWdom.trans (hdom.symm.trans hDdom.symm)
  have hdiag : ∀ u ∈ W.domain, W.form u u = D.form u u := by
    intro u hu
    have huF : u ∈ F.domain := hWdom ▸ hu
    have huE : u ∈ E.domain := hdom.symm ▸ huF
    have hm := energy_measure_eq_of_energy_eq E F ΓE ΓF Q hcore hbase u huE
    have hd := hWdiag u huF
    rw [W.energy_of_mem hu, ← hm, ← hDdiag u huE] at hd
    exact EReal.coe_injective hd
  have henergies : ∀ u, limitFormEnergy Grho u = limitFormEnergy Gdeleted u := by
    intro u
    rw [← hWenergy u, ← hDenergy u]
    exact extended_energy_eq_of_domain_and_diagonal_eq W.toClosedForm D.toClosedForm
      hWDdom hdiag u
  apply _root_.SubdiffusiveProcess.Paper.prop_21_dual_energy_operator_unique Grho Gdeleted hGrhosym
    (fun f g => ?_) hGrhopos (hDresolvent.inner_self_nonneg le_rfl) henergies
  rw [real_inner_comm]
  exact (hDresolvent.inner_comm f g).symm

end SubdiffusiveProcess.WeightedLimitIdentification
