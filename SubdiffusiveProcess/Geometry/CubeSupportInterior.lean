import SubdiffusiveProcess.Geometry.Cube
import Mathlib
open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess


theorem ae_mem_centeredCube_of_support_closure_of_hyperplanes_null
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d))
    (hsupp : ν (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0) :
    ∀ᵐ x ∂ν, x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hclosure : ∀ᵐ x ∂ν, x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    ae_iff.2 hsupp
  have hlower (i : Fin d) :
      ∀ᵐ x ∂ν, z i - r / 2 ≤ x i := by
    have hclosed : IsClosed {x : SpatialCoordinates d | z i - r / 2 ≤ x i} :=
      isClosed_le continuous_const (continuous_apply i)
    have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        {x : SpatialCoordinates d | z i - r / 2 ≤ x i} := by
      rw [centeredCube_eq_pi z hr]
      intro x hx
      exact le_of_lt ((mem_pi.mp hx) i (by simp)).1
    have hclsub : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        {x : SpatialCoordinates d | z i - r / 2 ≤ x i} :=
      closure_minimal hsub hclosed
    filter_upwards [hclosure] with x hx
    exact hclsub hx
  have hupper (i : Fin d) :
      ∀ᵐ x ∂ν, x i ≤ z i + r / 2 := by
    have hclosed : IsClosed {x : SpatialCoordinates d | x i ≤ z i + r / 2} :=
      isClosed_le (continuous_apply i) continuous_const
    have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        {x : SpatialCoordinates d | x i ≤ z i + r / 2} := by
      rw [centeredCube_eq_pi z hr]
      intro x hx
      exact le_of_lt ((mem_pi.mp hx) i (by simp)).2
    have hclsub : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        {x : SpatialCoordinates d | x i ≤ z i + r / 2} :=
      closure_minimal hsub hclosed
    filter_upwards [hclosure] with x hx
    exact hclsub hx
  have hneq (i : Fin d) (c : ℝ) : ∀ᵐ x ∂ν, x i ≠ c := by
    apply ae_iff.2
    rw [show {x : SpatialCoordinates d | ¬x i ≠ c} = {x | x i = c} by
      ext x
      simp]
    exact hplanes i c
  filter_upwards [hclosure,
    ae_all_iff.2 hlower,
    ae_all_iff.2 hupper,
    ae_all_iff.2 (fun i => hneq i (z i - r / 2)),
    ae_all_iff.2 (fun i => hneq i (z i + r / 2))] with x hx hlow hupp hlowneq huppneq
  rw [centeredCube_eq_pi z hr]
  apply mem_pi.2
  intro i hi
  exact ⟨lt_of_le_of_ne (hlow i) (Ne.symm (hlowneq i)),
    lt_of_le_of_ne (hupp i) (huppneq i)⟩

end SubdiffusiveProcess
