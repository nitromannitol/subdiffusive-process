module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Paper.e5_bridge_fot_strong_locality
public import SubdiffusiveProcess.Paper.inputs_classical_fot_beurling_deny_relative_locality

@[expose] public section

/-! Classical Beurling--Deny locality on an open Euclidean state space.
The core and its locality are explicit premises; no model-specific locality is assumed or concluded. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- A regular form on an open Euclidean domain is strongly local when its continuous compactly supported core is local. -/
theorem inputs_classical_e5_relative_locality
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
    _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm := by
  have hfull : (volume.restrict (Q : Set (SpatialCoordinates d))) (Q : Set (SpatialCoordinates d))ᶜ = 0 := by
    rw [Measure.restrict_apply Q.isOpen.measurableSet.compl]
    simp
  exact e5_bridge_fot_strong_locality d Q F (Q : Set (SpatialCoordinates d)) Q.isOpen hfull _hcore
    (inputs_classical_fot_beurling_deny_relative_locality d Q F _hcore _hloc)

end SubdiffusiveProcess.Paper
