module

public import SubdiffusiveProcess.Variational.SourceObjectives

@[expose] public section

/-! # Bilinear algebra for relative coefficient perturbations

These identities use only symmetry and the displayed weak equations. They
apply to the actual Sobolev graph norm without a new inner-product instance.
-/

namespace SubdiffusiveProcess
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The common source or harmonic difference equation gives the perturbation identity. -/
theorem bilinear_solution_difference (E F : V →L[ℝ] V →L[ℝ] ℝ) (u v : V)
    (h : F v (v - u) = E u (v - u)) :
    F (v - u) (v - u) = -(F u (v - u) - E u (v - u)) := by
  rw [map_sub F v u, ContinuousLinearMap.sub_apply, h]
  ring

/-- A harmonic boundary response has the direct-response sign convention. -/
theorem bilinear_boundary_response_difference (E F : V →L[ℝ] V →L[ℝ] ℝ)
    (hF : ∀ x y, F x y = F y x) (u v : V) (h : F v (v - u) = 0) :
    F v v - E u u = (F u u - E u u) - F (v - u) (v - u) := by
  simp only [map_sub] at h
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hF u v]
  linarith

/-- A fixed-source response has the opposite coefficient-change sign. -/
theorem bilinear_source_response_difference (E F : V →L[ℝ] V →L[ℝ] ℝ)
    (hF : ∀ x y, F x y = F y x) (u v : V) (h : F v u = E u u) :
    F v v - E u u = F (v - u) (v - u) - (F u u - E u u) := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hF u v, h]
  ring

/-- The local quadratic triangle bound uses only positivity and symmetry. -/
theorem bilinear_quadratic_sub_le (E : V →L[ℝ] V →L[ℝ] ℝ)
    (hE : ∀ x y, E x y = E y x) (hn : ∀ x, 0 ≤ E x x) (u v : V) :
    E u u ≤ 2 * E v v + 2 * E (u - v) (u - v) := by
  have h := hn (u - (2 : ℝ) • v)
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at h ⊢
  rw [hE v u] at h ⊢
  linarith

end SubdiffusiveProcess
