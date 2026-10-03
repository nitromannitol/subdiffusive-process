module

public import SubdiffusiveProcess.DirichletForm.ContinuousTraceResponse
public import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The local trace response depends only on the continuous representative of
the source on the killed cube; representatives chosen in different cells agree. -/
theorem goodext_common_response
    (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure F) (u : DomainL2 Q)
    (U V : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
    (hV : ContinuousOn V (closure (Q : Set (SpatialCoordinates d))))
    (hUr : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U)
    (hVr : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V)
    (q : Set (SpatialCoordinates d)) (hq : q ⊆ Q) :
    Gamma.continuousTraceValues (closure (Q : Set (SpatialCoordinates d))) q U =
      Gamma.continuousTraceValues (closure (Q : Set (SpatialCoordinates d))) q V := by
  have heq := eqOn_closure_of_ae_eq_restrict Q.isOpen hU hV (hUr.symm.trans hVr)
  have hfront : frontier q ⊆ closure (Q : Set (SpatialCoordinates d)) :=
    frontier_subset_closure.trans (closure_mono hq)
  ext e
  constructor
  · rintro ⟨v, W, hv, hW, hWr, htrace, henergy⟩
    exact ⟨v, W, hv, hW, hWr, fun x hx => (htrace x hx).trans (heq (hfront hx)), henergy⟩
  · rintro ⟨v, W, hv, hW, hWr, htrace, henergy⟩
    exact ⟨v, W, hv, hW, hWr, fun x hx => (htrace x hx).trans (heq (hfront hx)).symm, henergy⟩

end Paper
