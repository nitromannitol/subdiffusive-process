module

public import SubdiffusiveProcess.Sobolev.WeakGradientUpstream

@[expose] public section

open MeasureTheory Set TopologicalSpace

namespace SubdiffusiveProcess

/-- Every local weak Sobolev datum supplies the imported H1 carrier with exactly its
function and gradient representatives. -/
theorem exists_nativeH1Function_of_weakSobolevGraph
    {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (u : weakSobolevGraph Ω) :
    ∃ v : Homogenization.H1Function (Ω : Set (SpatialCoordinates d)),
      (v : SpatialCoordinates d → ℝ) = (fun x => u.val.1 x) ∧
      v.grad = (fun x i => u.val.2 i x) := by
  have hweak :
      Homogenization.HasWeakGradientOn (Ω : Set (SpatialCoordinates d))
        (fun x => u.val.1 x) (fun x i => u.val.2 i x) :=
    (mem_weakSobolevGraph_iff_hasWeakGradientOn u.val).mp u.property
  refine ⟨
    { toFun := fun x => u.val.1 x
      grad := fun x i => u.val.2 i x
      memL2 := Lp.memLp _
      gradMemL2 := ?_
      hasWeakGradient := hweak },
    rfl, rfl⟩
  intro i
  exact Lp.memLp _

end SubdiffusiveProcess
