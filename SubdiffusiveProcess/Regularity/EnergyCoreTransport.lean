module

public import SubdiffusiveProcess.DirichletForm.EnergyEquality
public import SubdiffusiveProcess.DirichletForm.Regular

@[expose] public section

open MeasureTheory

noncomputable section
namespace SubdiffusiveProcess.Regularity

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- A core transfers to a closed form with exactly the same extended energy. -/
theorem isCoreOn_of_energy_eq
    {E F : DirichletForm.ClosedForm m}
    (henergy : ∀ u, E.energy u = F.energy u)
    {U : Set X} {C : Set (Lp ℝ 2 m)}
    (hcore : DirichletForm.IsCoreOn F U C) :
    DirichletForm.IsCoreOn E U C := by
  have hmem := DirichletForm.ClosedForm.mem_domain_iff_of_energy_eq henergy
  refine ⟨?_, ?_, hcore.denseUniform⟩
  · intro u hu
    obtain ⟨huF, hrep⟩ := hcore.memCoreOn u hu
    exact ⟨(hmem u).mpr huF, hrep⟩
  · intro u hu epsilon hepsilon
    obtain ⟨w, hw, hsmall⟩ := hcore.denseEnergy u ((hmem u).mp hu) epsilon hepsilon
    have hwE := (hmem w).mpr (hcore.memCoreOn w hw).mem_domain
    have heq : E.energyNormSq (u - w) = F.energyNormSq (u - w) := by
      unfold DirichletForm.ClosedForm.energyNormSq
      rw [DirichletForm.ClosedForm.form_self_eq_of_energy_eq henergy (E.domain.sub_mem hu hwE)]
    exact ⟨w, hw, heq ▸ hsmall⟩

/-- Regularity transfers along equality of the literal extended energies. -/
theorem isRegular_of_energy_eq
    {E F : DirichletForm.ClosedForm m}
    (henergy : ∀ u, E.energy u = F.energy u)
    (hregular : DirichletForm.IsRegular F) :
    DirichletForm.IsRegular E := by
  obtain ⟨U, hU, hmass, C, hcore⟩ := hregular
  exact ⟨U, hU, hmass, C, isCoreOn_of_energy_eq henergy hcore⟩

end SubdiffusiveProcess.Regularity
