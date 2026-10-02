import SubdiffusiveProcess.DirichletForm.Energy

/-! Transport of domain and contraction properties across equality of extended energies.
The conclusions concern the actual domain forms; no equality of arbitrary
bilinear values outside their domains is asserted.
-/

open MeasureTheory
noncomputable section
namespace DirichletForm.ClosedForm
variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- Equal extended energies have the same form domain. -/
theorem mem_domain_iff_of_energy_eq {E F : ClosedForm m}
    (h : ∀ u, E.energy u = F.energy u) (u : Lp ℝ 2 m) :
    u ∈ E.domain ↔ u ∈ F.domain := by
  rw [← E.energy_lt_top_iff, ← F.energy_lt_top_iff, h u]

/-- Equal extended energies have the same quadratic form value on their domain. -/
theorem form_self_eq_of_energy_eq {E F : ClosedForm m}
    (h : ∀ u, E.energy u = F.energy u) {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    E.form u u = F.form u u := by
  have hf := (mem_domain_iff_of_energy_eq h u).mp hu
  have he := h u
  rw [E.energy_of_mem hu, F.energy_of_mem hf] at he
  exact EReal.coe_injective he

/-- A scalar map operating on one form operates on every form with the same extended energy. -/
theorem operatesOn_of_energy_eq {E F : ClosedForm m}
    (h : ∀ u, E.energy u = F.energy u) {T : ℝ → ℝ} (hT : F.OperatesOn T) :
    E.OperatesOn T := by
  intro u hu v hv
  obtain ⟨hvF, hbound⟩ := hT u ((mem_domain_iff_of_energy_eq h u).mp hu) v hv
  have hvE := (mem_domain_iff_of_energy_eq h v).mpr hvF
  refine ⟨hvE, ?_⟩
  rw [form_self_eq_of_energy_eq h hvE, form_self_eq_of_energy_eq h hu]
  exact hbound

/-- The Markov realization of an energy functional transports to a given closed form with that energy. -/
def dirichletFormOfEnergyEq (E : ClosedForm m) (F : _root_.DirichletForm m)
    (h : ∀ u, E.energy u = F.toClosedForm.energy u) : _root_.DirichletForm m where
  toClosedForm := E
  markov := operatesOn_of_energy_eq h F.markov

/-- Normal contractions transport along the exact energy-preserving Dirichlet realization. -/
theorem hasNormalContractions_dirichletFormOfEnergyEq
    (E : ClosedForm m) (F : _root_.DirichletForm m)
    (h : ∀ u, E.energy u = F.toClosedForm.energy u)
    (hF : DirichletForm.HasNormalContractions F) :
    DirichletForm.HasNormalContractions (dirichletFormOfEnergyEq E F h) :=
  ⟨fun T hT => operatesOn_of_energy_eq h (hF.operatesOn T hT)⟩

end DirichletForm.ClosedForm
