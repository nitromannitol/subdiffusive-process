import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Paper.e5_fot_strongly_local
import SubdiffusiveProcess.Paper.inputs_classical_fot_energy_measure_qc

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- E5: FOT energy-measure existence and calculus on Euclidean open domains. -/
theorem inputs_classical_e5_energy (d : ℕ) (Ω : Opens (SpatialCoordinates d))
    (F : _root_.DirichletForm (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hreg : DirichletForm.IsRegular F.toClosedForm)
    (hloc : DirichletForm.IsStronglyLocal F.toClosedForm) :
    Nonempty (DirichletForm.EnergyMeasure F.toClosedForm) := by
  obtain ⟨U, hU, hfull, hcore⟩ := hreg
  have hfot : e5_fot_strongly_local F.toClosedForm U := by
    intro u hu v hv hucs c W hW hvcs huc
    obtain ⟨Ku, hKu, _, hKu0⟩ := hucs
    obtain ⟨Kv, hKv, hKvsub, hKv0⟩ := hvcs
    refine hloc u hu v hv ⟨Ku, hKu, hKu0⟩ ⟨Kv, hKv, hKv0⟩ c W hW ?_ huc
    filter_upwards [hKv0] with x hx hxW
    exact hx (fun hxK => hxW (hKvsub hxK).2)
  obtain ⟨Γ, _⟩ := inputs_classical_fot_energy_measure_qc d Ω F U hU hfull hcore hfot
  exact ⟨Γ⟩

end Paper
