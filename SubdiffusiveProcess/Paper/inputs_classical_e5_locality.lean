import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Paper.e5_bridge_fot_strong_locality
import SubdiffusiveProcess.Paper.inputs_classical_fot_beurling_deny_locality

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- E5: Beurling–Deny uniqueness on an arbitrary Euclidean open state space. -/
theorem inputs_classical_e5_locality (d : ℕ) (Ω : Opens (SpatialCoordinates d))
    (F : _root_.DirichletForm (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hreg : DirichletForm.IsRegular F.toClosedForm)
    (hloc : DirichletForm.IsStronglyLocalOnCore F.toClosedForm) :
    DirichletForm.IsStronglyLocal F.toClosedForm := by
  obtain ⟨U, hU, hfull, hcore⟩ := hreg
  exact e5_bridge_fot_strong_locality d Ω F U hU hfull hcore
    (inputs_classical_fot_beurling_deny_locality d Ω F ⟨U, hU, hfull, hcore⟩ hloc U hU hfull hcore)

end Paper
