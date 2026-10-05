module

public import SubdiffusiveProcess.DirichletForm.FOTLocality
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Paper.e5_fot_strongly_local

@[expose] public section

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- Strong locality on the continuous compactly supported core of an open
Euclidean state space extends to the form domain. -/
theorem inputs_classical_fot_beurling_deny_relative_locality
    (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (_hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (_hloc : ∀ u v : DomainL2 Q,
      F.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) u →
      F.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) :
    e5_fot_strongly_local F.toClosedForm (Q : Set (SpatialCoordinates d)) := by
  exact _root_.SubdiffusiveProcess.DirichletForm.stronglyLocalOn_of_core_locality F Q.isOpen _hcore _hloc

end SubdiffusiveProcess.Paper
