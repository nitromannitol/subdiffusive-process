module

public import SubdiffusiveProcess.Paper.inputs_classical_e6_stampacchia
public import SubdiffusiveProcess.Lane2.NativeBridge

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem inputs_contraction_graph (d : ℕ) (Ω : Opens (SpatialCoordinates d))
    (u : killedSobolevGraph Ω) (T : ℝ → ℝ) (hT : DirichletForm.IsNormalContraction T) :
    ∃ (v : killedSobolevGraph Ω) (theta : SpatialCoordinates d → ℝ),
      (∀ x, |theta x| ≤ 1) ∧
      ((v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => T (u.val.1 x)) ∧
      ((fun x i => v.val.2 i x) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => theta x • (fun i => u.val.2 i x)) := by
  obtain ⟨u₀, hu₀_val, hu₀_grad⟩ :=
    SubdiffusiveProcess.exists_nativeH10Function_of_killedSobolevGraph u
  obtain ⟨v₀, theta, htheta, hv₀, hgrad₀⟩ :=
    inputs_classical_e6_stampacchia d (Ω : Set (SpatialCoordinates d)) Ω.2
      u₀ T hT
  obtain ⟨v, hv_val, hv_grad⟩ :=
    SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10 v₀
  refine ⟨v, theta, htheta, ?_, ?_⟩
  · filter_upwards [hv_val, hv₀] with x hxv hx₀
    change v.val.1 x = v₀.toH1Function.toFun x at hxv
    change v₀.toH1Function.toFun x = T (u₀.toH1Function.toFun x) at hx₀
    have hu₀x : u₀.toH1Function.toFun x = u.val.1 x := by
      simpa using congrFun hu₀_val x
    calc
      v.val.1 x = v₀.toH1Function.toFun x := hxv
      _ = T (u₀.toH1Function.toFun x) := hx₀
      _ = T (u.val.1 x) := congrArg T hu₀x
  · have hcoord : ∀ i : Fin d,
        ((v.val.2 i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
          fun x => theta x * u.val.2 i x) := by
      intro i
      filter_upwards [hv_grad i, hgrad₀] with x hxv hx₀
      change v.val.2 i x = v₀.toH1Function.grad x i at hxv
      change v₀.toH1Function.grad x = theta x • u₀.toH1Function.grad x at hx₀
      have hu₀x : u₀.toH1Function.grad x i = u.val.2 i x := by
        simpa using congrFun (congrFun hu₀_grad x) i
      calc
        v.val.2 i x = v₀.toH1Function.grad x i := hxv
        _ = theta x * u₀.toH1Function.grad x i := by rw [hx₀]; simp
        _ = theta x * u.val.2 i x := by rw [hu₀x]
    have hcoord_all : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
        ∀ i : Fin d, v.val.2 i x = theta x * u.val.2 i x := by
      rw [ae_all_iff]
      exact hcoord
    filter_upwards [hcoord_all] with x hx
    funext i
    simpa using hx i

end Paper
