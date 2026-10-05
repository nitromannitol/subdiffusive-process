module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyExistence
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Paper.e5_fot_strongly_local
public import SubdiffusiveProcess.Paper.obl_BH_quasi_continuous_representative

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem inputs_classical_fot_energy_measure_qc (d : ℕ) (Ω : Opens (SpatialCoordinates d))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hUfull : (volume.restrict (Ω : Set (SpatialCoordinates d))) Uᶜ = 0)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm U C)
    (hfot : e5_fot_strongly_local F.toClosedForm U) :
    ∃ Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm,
      obl_BH_quasi_continuous_representative F Γ := by
  simpa only [_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.HasRepresentativeCalculus,
    obl_BH_quasi_continuous_representative] using
    _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.exists_energyMeasure_representative F
      (U := U) ⟨hU, hUfull, hcore, hfot⟩

end SubdiffusiveProcess.Paper
