import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Source-objective identities on normed vector spaces

Only bilinearity and the weak equation enter the gap identity. In particular
it applies to the concrete Sobolev graph, whose default norm is a graph norm,
without pretending that this norm is induced by an inner product.
-/

namespace SubdiffusiveProcess
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A symmetric bilinear weak equation gives the exact source-objective gap. -/
theorem bilinear_source_objective_gap (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (L : V →L[ℝ] ℝ) (u : V)
    (hu : ∀ v, B u v = L v) (v : V) :
    B u u - (2 * L v - B v v) = B (v - u) (v - u) := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hB v u, hu v, hu u]
  ring

/-- Orthogonality to the difference gives the exact affine energy gap. -/
theorem bilinear_affine_energy_gap (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (u v : V) (hu : B u (v - u) = 0) :
    B v v = B u u + B (v - u) (v - u) := by
  simp only [map_sub] at hu
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hB v u]
  linarith

end SubdiffusiveProcess
