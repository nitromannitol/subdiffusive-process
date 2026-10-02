import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Sobolev.NativeBoundaryResponse

/-! Native representatives recover their complete weak Sobolev data.
Only almost-everywhere values are prescribed; uniqueness of weak gradients
identifies the gradient class. No regularity estimate is asserted.
-/
open MeasureTheory Set TopologicalSpace Homogenization
noncomputable section
namespace SubdiffusiveProcess

/-- Every representative of a weak Sobolev datum is the literal value function of native H1 data representing the same graph element. -/
theorem exists_nativeH1Function_of_ae_representative
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (u : weakSobolevGraph Q)
    (U : SpatialCoordinates d → ℝ)
    (hU : (u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) :
    ∃ v : H1Function (Q : Set (SpatialCoordinates d)),
      v.toFun = U ∧ sobolevDataOfH1 v = u.val := by
  obtain ⟨v0, hv0, _⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  have hv0rep : U =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] v0.toFun := by
    rw [hv0]
    exact hU.symm
  let v := lane2_H1ofAEEq v0 U hv0rep
  have hf : (sobolevDataOfH1 v).1 = u.val.1 := by
    apply Lp.ext
    exact (sobolevDataOfH1_fst_coeFn v).trans hU.symm
  refine ⟨v, rfl, Prod.ext hf ?_⟩
  apply weakSobolevGraph_gradient_unique (u := u.val.1)
  · rw [← hf]
    exact sobolevDataOfH1_mem_weak v
  · exact u.property

end SubdiffusiveProcess
