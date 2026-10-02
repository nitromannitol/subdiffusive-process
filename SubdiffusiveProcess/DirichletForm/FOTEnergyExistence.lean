import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousLipschitz

open MeasureTheory Filter Set Topology
open scoped NNReal ContDiff

noncomputable section

namespace DirichletForm.FOTConstruction

theorem exists_energyMeasure_representative
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] {m : Measure X}
    (F : _root_.DirichletForm m) {U : Set X} (h : Data F U) :
    ∃ Γ : EnergyMeasure F.toClosedForm, HasRepresentativeCalculus F Γ := by
  obtain ⟨CΓ⟩ := exists_coreMeasure F h
  obtain ⟨Γ, _⟩ := exists_energyFamily F h CΓ
  obtain ⟨q⟩ := exists_representativeFamily h Γ
  obtain ⟨G, hG, _⟩ := Γ.exists_energyMeasure h q
  refine ⟨G, q.rep, q.measurable, q.ae_rep, ?_, ?_⟩
  · intro u hu K hK hK0
    rw [hG u hu]
    exact Γ.quasiContinuous_nullity h q hu hK hK0
  · intro u hu T hT hT0 D hD hderiv w hw hwae B hB
    rw [hG w hw, hG u hu]
    exact Γ.quasiContinuous_lipschitz_chain h q hu T hT hT0 D hD hderiv hw hwae hB

end DirichletForm.FOTConstruction
