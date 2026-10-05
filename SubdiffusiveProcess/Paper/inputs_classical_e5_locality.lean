module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Paper.e5_bridge_fot_strong_locality
public import SubdiffusiveProcess.Paper.inputs_classical_fot_beurling_deny_locality

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- E5: Beurling–Deny uniqueness on an arbitrary Euclidean open state space. -/
theorem inputs_classical_e5_locality (d : ℕ) (Ω : Opens (SpatialCoordinates d))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hreg : _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm)
    (hloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm) :
    _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm := by
  obtain ⟨U, hU, hfull, hcore⟩ := hreg
  exact e5_bridge_fot_strong_locality d Ω F U hU hfull hcore
    (inputs_classical_fot_beurling_deny_locality d Ω F ⟨U, hU, hfull, hcore⟩ hloc U hU hfull hcore)

end SubdiffusiveProcess.Paper
