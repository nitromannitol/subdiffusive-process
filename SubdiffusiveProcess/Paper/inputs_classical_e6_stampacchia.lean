module

public import Homogenization.Sobolev.H1.Definitions
public import SubdiffusiveProcess.DirichletForm.Basic
public import SubdiffusiveProcess.Stampacchia.Assembly

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- E6: Stampacchia composition and zero-trace preservation on any open domain. -/
theorem inputs_classical_e6_stampacchia (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U)
    (u : H10Function U) (T : ℝ → ℝ) (hT : DirichletForm.IsNormalContraction T) :
    ∃ (v : H10Function U) (theta : Vec d → ℝ),
      (∀ x, |theta x| ≤ 1) ∧
      (v.toH1Function.toFun =ᵐ[volume.restrict U] fun x => T (u.toH1Function.toFun x)) ∧
      (v.toH1Function.grad =ᵐ[volume.restrict U] fun x => theta x • u.toH1Function.grad x) := by
  exact SubdiffusiveProcess.Stampacchia.stampacchia_general hU u T hT.map_zero hT.dist_le

end Paper
