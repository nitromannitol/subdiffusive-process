import SubdiffusiveProcess.Paper.lem_truncation
import SubdiffusiveProcess.Paper.obl_BH_compact_preimage_nullity
import SubdiffusiveProcess.Paper.obl_BH_energy_measure_convergence
import SubdiffusiveProcess.Paper.limit_form_package_side
import SubdiffusiveProcess.Section9.CoreAlgebraOfRegular
import SubdiffusiveProcess.DirichletForm.KilledCoreClosure
import Mathlib.Topology.TietzeExtension





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- Extend a closed-cube representative and transfer both Bouleau--Hirsch
identities along the actual energy-measure support. -/
theorem aux_mfd_prop_boundary_bh_on_closure
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (v : DomainL2 Q) (hv : v ∈ E.domain)
    (vc : SpatialCoordinates d → ℝ) (hc : ContinuousOn vc (closure (Q : Set (SpatialCoordinates d))))
    (hrep : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc) :
    (∀ N : Set ℝ, MeasurableSet N → volume N = 0 → Gamma.measure v (vc ⁻¹' N) = 0) ∧
    (∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
      ∀ Tderiv : ℝ → ℝ, Measurable Tderiv →
      (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
      ∀ w : DomainL2 Q, w ∈ E.domain →
      ((w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        fun x => T (vc x)) →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        (Gamma.measure w B).toReal = ∫ x in B, (Tderiv (vc x)) ^ 2 ∂(Gamma.measure v)) := by
  classical
  let f : C(closure (Q : Set (SpatialCoordinates d)), ℝ) :=
    ⟨_, continuousOn_iff_continuous_restrict.mp hc⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq isClosed_closure f
  have hgv : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), g x = vc x := by
    intro x hx
    exact congrArg (fun k : C(closure (Q : Set (SpatialCoordinates d)), ℝ) => k ⟨x, hx⟩) hg
  have hvol : (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc :=
    (ae_restrict_mem Q.isOpen.measurableSet).mono fun x hx => hgv x (subset_closure hx)
  have hgamma : (g : SpatialCoordinates d → ℝ) =ᵐ[Gamma.measure v] vc := by
    obtain ⟨C, hC⟩ := hcore
    have hs := aux_limit_form_package_energy_measure_support Gamma Q.isOpen.measurableSet hC hv
    exact (ae_iff.mpr hs).mono fun x hx => hgv x (subset_closure hx)
  have halg := SubdiffusiveProcess.Section9.isCoreAlgebra_of_isRegular E
    (aux_limit_form_package_isRegular_of_core Q E.toClosedForm hcore)
  have hnc := DirichletForm.hasNormalContractions E
  refine ⟨?_, ?_⟩
  · intro N hN hN0
    have hnull := obl_BH_compact_preimage_nullity E Gamma halg hnc v hv g g.continuous
      (hrep.trans hvol.symm) N hN hN0
    have hs : ((g : SpatialCoordinates d → ℝ) ⁻¹' N) =ᵐ[Gamma.measure v] vc ⁻¹' N := by
      filter_upwards [hgamma] with x hx
      change (g x ∈ N) = (vc x ∈ N)
      rw [hx]
    exact (measure_congr hs).symm.trans hnull
  · intro T hT hT0 Tderiv hm hd w hw hwrep B hB
    have h := obl_BH_energy_measure_convergence E Gamma halg hnc v hv g g.continuous
      (hrep.trans hvol.symm) T hT hT0 Tderiv hm hd w hw
      (hwrep.trans (hvol.symm.mono fun x hx => congrArg T hx)) B hB
    rw [integral_congr_ae ((ae_restrict_of_ae hgamma).mono fun x hx => by rw [hx])] at h
    exact h

/-- The zero-trace supplier is proved from the form's actual core and the
proved BH children; no nullity or chain-rule result is carried by the caller. -/
theorem aux_mfd_prop_boundary_zero_trace
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hDq : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (v : DomainL2 (centeredCube zQ R hR)) (hv : v ∈ E.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hc : ContinuousOn vc (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hrep : (v : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] vc)
    (hzero : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), vc x = 0)
    (vq : DomainL2 (centeredCube zQ R hR))
    (hvq : (vq : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))]
        (closure (centeredCube zq r hr : Set (SpatialCoordinates d))).indicator vc) :
    vq ∈ Dq ∧ E.form vq vq =
      (Gamma.measure v (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal := by
  obtain ⟨hnull, hchain⟩ := aux_mfd_prop_boundary_bh_on_closure _ E Gamma hcore v hv vc hc hrep
  have h := lem_truncation d hd zQ zq R r hR hr hqQ E Gamma
    (DirichletForm.hasNormalContractions E)
    (SubdiffusiveProcess.Section9.isCoreAlgebra_of_isRegular E
      (aux_limit_form_package_isRegular_of_core _ E.toClosedForm hcore))
    hcore Dq hDq v hv vc hc hrep hzero hnull hchain vq hvq
  exact ⟨h.1, h.2.1⟩

end Paper
