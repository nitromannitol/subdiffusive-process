import Mathlib.Tactic
import SubdiffusiveProcess.Compactness.SequentialCompactness
import SubdiffusiveProcess.DirichletForm.FOTProduct
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Sobolev.CompactResponses
import SubdiffusiveProcess.Paper.lem_truncation
import SubdiffusiveProcess.Paper.obl_BH_compact_preimage_nullity
import SubdiffusiveProcess.Paper.obl_BH_energy_measure_convergence
import SubdiffusiveProcess.Paper.prop_conc_core_measure_data

/-! Deterministic prop conc boundary truncation data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace Paper
noncomputable section

/-- Extracted continuous energy representative argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_boundary_truncation_continuous_energy_representative
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z R hR : Set (SpatialCoordinates d)) C)
    (v : DomainL2 (centeredCube z R hR)) (hv : v ∈ E.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvc : ContinuousOn vc (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hrep : ⇑v =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vc) :
    ∃ V : SpatialCoordinates d → ℝ, Continuous V ∧
      (⇑v =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] V) ∧
      (V =ᵐ[Gamma.measure v] vc) := by
  let Qs : Set (SpatialCoordinates d) := centeredCube z R hR
  have hQc : IsCompact (closure Qs) := lane2_isCompact_closure_centeredCube z hR
  letI instExtract1 : CompactSpace (closure Qs) := isCompact_iff_compactSpace.mp hQc
  let fQ : C(closure Qs, ℝ) := ⟨fun x => vc x, hvc.restrict⟩
  let fQb : BoundedContinuousFunction (closure Qs) ℝ :=
    BoundedContinuousFunction.mkOfCompact fQ
  obtain ⟨V, _hVnorm, hVeq⟩ :=
    BoundedContinuousFunction.exists_norm_eq_restrict_eq_of_closed fQb isClosed_closure
  have heq : ∀ x ∈ closure Qs, V x = vc x := by
    intro x hx
    have hx' := congrArg
      (fun f : BoundedContinuousFunction (closure Qs) ℝ => f ⟨x, hx⟩) hVeq
    change V x = vc x at hx'
    exact hx'
  have hQmeas : MeasurableSet Qs := (centeredCube z R hR).isOpen.measurableSet
  refine ⟨V, V.continuous, ?_, ?_⟩
  · filter_upwards [hrep, ae_restrict_mem hQmeas] with x hx hxQ
    exact hx.trans (heq x (subset_closure hxQ)).symm
  · obtain ⟨C, hC⟩ := hcore
    have hsupp : Gamma.measure v Qsᶜ = 0 :=
      Paper.aux_prop_conc_core_measure_data_energy_measure_support Gamma hQmeas hC hv
    have hmem : ∀ᵐ x ∂Gamma.measure v, x ∈ Qs := by
      exact ae_iff.mpr hsupp
    filter_upwards [hmem] with x hx
    exact heq x (subset_closure hx)

/-- Extracted boundary BH argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_boundary_truncation_boundary_BH
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z R hR : Set (SpatialCoordinates d)) C)
    (v : DomainL2 (centeredCube z R hR)) (hv : v ∈ E.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvc : ContinuousOn vc (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hrep : ⇑v =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vc) :
    (∀ N : Set ℝ, MeasurableSet N → volume N = 0 →
      Gamma.measure v (vc ⁻¹' N) = 0) ∧
    (∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
      ∀ Tderiv : ℝ → ℝ, Measurable Tderiv →
      (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
      ∀ w : DomainL2 (centeredCube z R hR), w ∈ E.domain →
        (⇑w =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          fun x => T (vc x)) →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        (Gamma.measure w B).toReal =
          ∫ x in B, (Tderiv (vc x)) ^ 2 ∂(Gamma.measure v)) := by
  obtain ⟨V, hV, hVrep, hVenergy⟩ :=
    Paper.aux_prop_conc_boundary_truncation_continuous_energy_representative z R hR E Gamma hcore v hv vc hvc hrep
  have halg := Paper.prop_conc_core_measure_data (centeredCube z R hR) E hcore
  have hnc := DirichletForm.hasNormalContractions E
  constructor
  · intro N hN hN0
    have heq : (vc ⁻¹' N) =ᵐ[Gamma.measure v] (V ⁻¹' N) := by
      filter_upwards [hVenergy] with x hx
      change (vc x ∈ N) = (V x ∈ N)
      rw [hx]
    rw [measure_congr heq]
    exact obl_BH_compact_preimage_nullity E Gamma halg hnc v hv V hV hVrep N hN hN0
  · intro T hLip hT0 Tderiv hdm hdv w hw hwrep B hB
    have hwrepV : ⇑w =ᵐ[volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))] fun x => T (V x) := by
      filter_upwards [hwrep, hrep, hVrep] with x hwx hvx hVx
      exact hwx.trans (congrArg T (hvx.symm.trans hVx))
    have hchain := obl_BH_energy_measure_convergence E Gamma halg hnc v hv V hV hVrep
      T hLip hT0 Tderiv hdm hdv w hw hwrepV B hB
    rw [hchain]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hVenergy] with x hx
    rw [hx]

/-- Extracted boundary truncation argument from the pre-convergence deterministic proof. -/
theorem prop_conc_boundary_truncation
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
    (hkilled : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (v : DomainL2 (centeredCube zQ R hR)) (hv : v ∈ E.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvc : ContinuousOn vc (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hrep : ⇑v =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] vc)
    (hvanish : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), vc x = 0)
    (vq : DomainL2 (centeredCube zQ R hR))
    (hvq : ⇑vq =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))]
      (closure (centeredCube zq r hr : Set (SpatialCoordinates d))).indicator vc) :
    vq ∈ Dq ∧ E.form vq vq =
      (Gamma.measure v (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal := by
  obtain ⟨hnull, hchain⟩ := Paper.aux_prop_conc_boundary_truncation_boundary_BH zQ R hR E Gamma hcore v hv vc hvc hrep
  have h := lem_truncation d hd zQ zq R r hR hr hqQ E Gamma
    (DirichletForm.hasNormalContractions E)
    (Paper.prop_conc_core_measure_data (centeredCube zQ R hR) E hcore)
    hcore Dq hkilled v hv vc hvc hrep hvanish hnull hchain vq hvq
  exact ⟨h.1, h.2.1⟩

end
end Paper
