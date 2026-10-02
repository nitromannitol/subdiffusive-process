import SubdiffusiveProcess.DirichletForm.EnergyEquality
import SubdiffusiveProcess.DirichletForm.EnergyMeasureScaling
import SubdiffusiveProcess.DirichletForm.Resolvent

/-! Unweighted quadratic identification determines the entire extended energy and
the regular energy measures on the common domain. -/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace SubdiffusiveProcess.AuditRepairs

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- Agreement of domains and diagonal form values identifies the extended energies. -/
theorem extended_energy_eq_of_domain_and_diagonal_eq
    (E F : DirichletForm.ClosedForm m) (hdom : E.domain = F.domain)
    (hdiag : ∀ u ∈ E.domain, E.form u u = F.form u u) (u : Lp ℝ 2 m) :
    E.energy u = F.energy u := by
  by_cases hu : u ∈ E.domain
  · rw [E.energy_of_mem hu, F.energy_of_mem (hdom ▸ hu), hdiag u hu]
  · rw [E.energy_of_notMem hu, F.energy_of_notMem (hdom ▸ hu)]

/-- Only the quadratic values of an inverse enter its dual extended energy. -/
theorem dual_energy_eq_of_quadratic_eq
    (G F : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (h : ∀ f, inner ℝ f (G f) = inner ℝ f (F f)) (u : Lp ℝ 2 m) :
    DirichletForm.dualEnergy G u = DirichletForm.dualEnergy F u := by
  simp only [DirichletForm.dualEnergy, h]

variable [TopologicalSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X] [OpensMeasurableSpace X]

/-- Equal extended energies identify the regular diagonal energy measures on their
common domain. The core hypothesis supplies the uniqueness input. -/
theorem energy_measure_eq_of_energy_eq
    (E F : _root_.DirichletForm m)
    (ΓE : DirichletForm.EnergyMeasure E.toClosedForm)
    (ΓF : DirichletForm.EnergyMeasure F.toClosedForm)
    (Q : Opens X)
    (hcore : ∃ C : Set (Lp ℝ 2 m),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set X) C)
    (henergy : ∀ u, E.energy u = F.energy u)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain) : ΓE.measure u = ΓF.measure u := by
  obtain ⟨C, hC⟩ := hcore
  have hdom : F.domain = E.domain := by
    ext v
    exact (DirichletForm.ClosedForm.mem_domain_iff_of_energy_eq henergy v).symm
  have hform : ∀ v ∈ E.domain, F.form v v = (1 : ℝ) * E.form v v := by
    intro v hv
    simpa only [one_mul] using
      (DirichletForm.ClosedForm.form_self_eq_of_energy_eq henergy hv).symm
  have h := ΓE.measure_eq_smul_of_form_scale ΓF Q hC zero_lt_one hdom hform hu
  simpa only [ENNReal.ofReal_one, one_smul] using h.symm

/-- Polarization identifies all cross energy measures from the diagonal equality. -/
theorem cross_energy_measure_eq_of_energy_eq
    (E F : _root_.DirichletForm m)
    (ΓE : DirichletForm.EnergyMeasure E.toClosedForm)
    (ΓF : DirichletForm.EnergyMeasure F.toClosedForm)
    (Q : Opens X)
    (hcore : ∃ C : Set (Lp ℝ 2 m),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set X) C)
    (henergy : ∀ u, E.energy u = F.energy u)
    (u v : Lp ℝ 2 m) (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    ΓE.cross u v = ΓF.cross u v := by
  have hmem := DirichletForm.ClosedForm.mem_domain_iff_of_energy_eq henergy
  have hFu := (hmem u).mp hu
  have hFv := (hmem v).mp hv
  ext B hB
  rw [ΓE.cross_eq_polarization hu hv, ΓF.cross_eq_polarization hFu hFv,
    ΓE.cross_self (u + v) (E.domain.add_mem hu hv) B hB,
    ΓE.cross_self (u - v) (E.domain.sub_mem hu hv) B hB,
    ΓF.cross_self (u + v) (F.domain.add_mem hFu hFv) B hB,
    ΓF.cross_self (u - v) (F.domain.sub_mem hFu hFv) B hB,
    energy_measure_eq_of_energy_eq E F ΓE ΓF Q hcore henergy (u + v)
      (E.domain.add_mem hu hv),
    energy_measure_eq_of_energy_eq E F ΓE ΓF Q hcore henergy (u - v)
      (E.domain.sub_mem hu hv)]

end SubdiffusiveProcess.AuditRepairs
