module

public import Mathlib.Tactic
public import SubdiffusiveProcess.Compactness.SequentialCompactness
public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Paper.energy_order_of_form_order

@[expose] public section

/-! Deterministic prop conc core measure data data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Extracted energy measure support argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_core_measure_data_energy_measure_support
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}
    {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm mu} (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    {U : Set X} (hU : MeasurableSet U) {Cc : Set (Lp ℝ 2 mu)}
    (hCc : _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E U Cc) {u : Lp ℝ 2 mu} (hu : u ∈ E.domain) :
    Gamma.measure u Uᶜ = 0 := by
  have hsqrt : Real.sqrt (Gamma.measure u Uᶜ).toReal ≤ 0 := by
    refine le_of_forall_pos_le_add fun eps heps => ?_
    obtain ⟨w, hwC, hsmall⟩ := hCc.denseEnergy u hu (eps ^ 2) (sq_pos_of_pos heps)
    have hw := hCc.memCoreOn w hwC
    have hw0 : Gamma.measure w Uᶜ = 0 := by
      obtain ⟨hwE, wc, hwc, _hwcompact, hwsupport, hwae⟩ := hw
      exact measure_mono_null (compl_subset_compl.mpr hwsupport)
        (Gamma.measure_compl_tsupport w hwE wc hwc hwae)
    have hdiff := E.domain.sub_mem hu hw.mem_domain
    have hbound : (Gamma.measure (u - w) Uᶜ).toReal ≤ eps ^ 2 :=
      (Gamma.toReal_measure_le_form hdiff Uᶜ).trans
        (E.form_le_energyNormSq.trans hsmall.le)
    have hs := aux_energy_order_of_form_order_sqrt_le Gamma hu hw.mem_domain hU.compl
    rw [hw0, ENNReal.toReal_zero, Real.sqrt_zero, zero_add] at hs
    exact (hs.trans (Real.sqrt_le_sqrt hbound)).trans_eq
      (by rw [Real.sqrt_sq heps.le, zero_add])
  have hz : (Gamma.measure u Uᶜ).toReal = 0 := by
    have hs0 := le_antisymm hsqrt (Real.sqrt_nonneg _)
    have hsq := Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (Gamma.measure u Uᶜ).toReal)
    rw [hs0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
    exact hsq.symm
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (Gamma.measure_ne_top hu Uᶜ)

/-- Extracted energy coe argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_core_measure_data_energy_coe {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) (hu : u ∈ limitFormDomain G) :
    limitFormEnergy G u = ((limitFormEnergy G u).toReal : EReal) := by
  have hu' : limitFormEnergy G u < ⊤ := hu
  exact (EReal.coe_toReal (ne_of_lt hu')
    (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg G u)))).symm

/-- Extracted isRegular of core argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_core_measure_data_isRegular_of_core
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F (Q : Set (SpatialCoordinates d)) C) :
    _root_.SubdiffusiveProcess.DirichletForm.IsRegular F := by
  refine ⟨Q, Q.isOpen, ?_, hcore⟩
  rw [Measure.restrict_apply Q.isOpen.measurableSet.compl]
  simp only [compl_inter_self, measure_empty]

/-- Extracted energy measure of locality argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_core_measure_data_energy_measure_of_locality
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (EM : _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) :
    ∃ Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm,
      ∀ u ∈ F.domain,
        Gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
  obtain ⟨Gamma⟩ := EM.exists_energyMeasure
    (_root_.SubdiffusiveProcess.Paper.aux_prop_conc_core_measure_data_isRegular_of_core (centeredCube z r hr) F.toClosedForm hcore) hloc
  obtain ⟨C, hC⟩ := hcore
  exact ⟨Gamma, fun u hu => _root_.SubdiffusiveProcess.Paper.aux_prop_conc_core_measure_data_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC hu⟩

/-- Extracted domain mem of energy argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_core_measure_data_domain_mem_of_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hE : ∀ u, E.energy u = limitFormEnergy G u)
    {u : DomainL2 Q} (hu : u ∈ limitFormDomain G) : u ∈ E.domain := by
  apply E.mem_domain_of_energy_lt_top
  rw [hE]
  exact hu

/-- Extracted core dense of isCoreOn argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_core_measure_data_core_dense_of_isCoreOn
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E (Q : Set (SpatialCoordinates d)) C) :
    ∀ u ∈ limitFormDomain G, ∀ eps : ℝ, 0 < eps →
      ∃ p : DomainL2 Q, MemFormCore G p ∧ ‖p - u‖ ≤ eps ∧
        limitFormEnergy G (p - u) ≤ ((eps : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := hcore
  intro u hu eps heps
  have huE : u ∈ E.domain := E.mem_domain_of_energy_lt_top (by rw [hE]; exact hu)
  obtain ⟨p, hpC, hsmall⟩ := hC.denseEnergy u huE (min (eps ^ 2) eps)
    (lt_min (sq_pos_of_pos heps) heps)
  have hp := hC.memCoreOn p hpC
  have hpu := E.domain.sub_mem hp.mem_domain huE
  rw [E.energyNormSq_sub_comm huE hp.mem_domain] at hsmall
  have hnormsq := (E.sq_norm_le_energyNormSq hpu).trans
    (hsmall.le.trans (min_le_left _ _))
  have hform := E.form_le_energyNormSq.trans (hsmall.le.trans (min_le_right _ _))
  refine ⟨p, ⟨?_, hp.2⟩, ?_, ?_⟩
  · show limitFormEnergy G p < ⊤
    rw [← hE]
    exact (E.energy_lt_top_iff p).mpr hp.mem_domain
  · nlinarith only [hnormsq, norm_nonneg (p - u), heps]
  · rw [← hE, E.energy_of_mem hpu]
    exact EReal.coe_le_coe_iff.mpr hform

/-- Extracted core algebra argument from the pre-convergence deterministic proof. -/
theorem prop_conc_core_measure_data
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (Q : Set (SpatialCoordinates d)) C) :
    _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra E.toClosedForm :=
  ⟨_root_.SubdiffusiveProcess.Paper.aux_prop_conc_core_measure_data_isRegular_of_core Q E.toClosedForm hcore,
    _root_.SubdiffusiveProcess.DirichletForm.mul_mem E, _root_.SubdiffusiveProcess.DirichletForm.comp_mem E,
    _root_.SubdiffusiveProcess.DirichletForm.mul_comp_mem E, _root_.SubdiffusiveProcess.DirichletForm.mul_mem_of_bounded E⟩

end
end SubdiffusiveProcess.Paper
