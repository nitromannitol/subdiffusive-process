import SubdiffusiveProcess.DirichletForm.FOTEnergyExistence
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Paper.e5_fot_strongly_local
import SubdiffusiveProcess.Paper.obl_BH_quasi_continuous_representative

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem inputs_classical_fot_energy_measure_qc (d : ℕ) (Ω : Opens (SpatialCoordinates d))
    (F : _root_.DirichletForm (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hUfull : (volume.restrict (Ω : Set (SpatialCoordinates d))) Uᶜ = 0)
    (hcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm U C)
    (hfot : e5_fot_strongly_local F.toClosedForm U) :
    ∃ Γ : DirichletForm.EnergyMeasure F.toClosedForm,
      obl_BH_quasi_continuous_representative F Γ := by
  simpa only [DirichletForm.FOTConstruction.HasRepresentativeCalculus,
    obl_BH_quasi_continuous_representative] using
    DirichletForm.FOTConstruction.exists_energyMeasure_representative F
      (U := U) ⟨hU, hUfull, hcore, hfot⟩

end Paper
