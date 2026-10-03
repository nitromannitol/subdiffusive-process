module

public import SubdiffusiveProcess.DirichletForm.FOTLocality
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Paper.e5_fot_strongly_local

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Strong locality on a regular core extends to the domain by core cutoffs,
bounded approximation and closed-form lower semicontinuity. -/
theorem inputs_classical_fot_beurling_deny_locality (d : ℕ) (Ω : Opens (SpatialCoordinates d))
    (F : _root_.DirichletForm (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hreg : DirichletForm.IsRegular F.toClosedForm)
    (hloc : DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hUfull : (volume.restrict (Ω : Set (SpatialCoordinates d))) Uᶜ = 0)
    (hcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm U C) :
    e5_fot_strongly_local F.toClosedForm U := by
  clear hreg hUfull
  apply DirichletForm.stronglyLocalOn_of_core_locality F hU hcore
  intro u v hu hv uc vc huae hvae huc hvc _ hvcCompact _ _ c W hW hvcW hconstant
  exact hloc u v hu.memCore hv.memCore uc vc huae hvae huc hvc hvcCompact
    c W hW hvcW hconstant

end Paper
