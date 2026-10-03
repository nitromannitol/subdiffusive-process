module

public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import Mathlib.Topology.Piecewise

@[expose] public section

/-! Continuous zero extension of a continuous boundary-zero representative.
The result identifies the existing L2 class; it does not assert Sobolev regularity.
-/
open Set MeasureTheory TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess

/-- A continuous representative vanishing on the frontier extends continuously by zero. -/
theorem continuous_zero_extension_of_frontier_zero
    {d : ℕ} (Q : Opens (SpatialCoordinates d)) (u : DomainL2 Q)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
    (hrep : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U)
    (hzero : ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) :
    ∃ V : SpatialCoordinates d → ℝ, Continuous V ∧
      (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
      ∀ x ∉ (Q : Set (SpatialCoordinates d)), V x = 0 := by
  classical
  let V := (Q : Set (SpatialCoordinates d)).piecewise U (fun _ => 0)
  refine ⟨V, continuous_piecewise hzero hU continuousOn_const, ?_, ?_⟩
  · filter_upwards [hrep, self_mem_ae_restrict Q.isOpen.measurableSet] with x hx hxQ
    simpa only [V, Set.piecewise, if_pos hxQ] using hx
  · intro x hx
    simp only [V, Set.piecewise, if_neg hx]

end SubdiffusiveProcess
