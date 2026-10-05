module

public import SubdiffusiveProcess.DirichletForm.Energy

@[expose] public section

/-! Algebra of affine orthogonal projection for a closed symmetric form.
Existence is an explicit Hilbert-space input; no spatial or probabilistic estimate is claimed. -/
open MeasureTheory
namespace SubdiffusiveProcess.DirichletForm.ClosedForm
noncomputable section
variable {X : Type*} [MeasurableSpace X] {mu : Measure X}

/-- The affine projection preserves the trace class and is orthogonal to the variation space. -/
def IsAffineProjection (E : ClosedForm mu) (V : Submodule ℝ (Lp ℝ 2 mu))
    (b u : Lp ℝ 2 mu) : Prop :=
  u ∈ E.domain ∧ u - b ∈ V ∧ ∀ v ∈ V, E.form u v = 0

/-- Affine projections add when their boundary data add. -/
theorem IsAffineProjection.add
    {E : ClosedForm mu} {V : Submodule ℝ (Lp ℝ 2 mu)} (hV : V ≤ E.domain)
    {b c u v : Lp ℝ 2 mu} (hu : E.IsAffineProjection V b u)
    (hv : E.IsAffineProjection V c v) : E.IsAffineProjection V (b + c) (u + v) := by
  refine ⟨E.domain.add_mem hu.1 hv.1, ?_, ?_⟩
  · have h := V.add_mem hu.2.1 hv.2.1
    convert h using 1 ; abel
  · intro w hw
    rw [E.form_add_left u hu.1 v hv.1 w (hV hw), hu.2.2 w hw, hv.2.2 w hw, add_zero]

/-- Affine projection commutes with multiplication of the boundary data by a real scalar. -/
theorem IsAffineProjection.smul
    {E : ClosedForm mu} {V : Submodule ℝ (Lp ℝ 2 mu)} (hV : V ≤ E.domain)
    {b u : Lp ℝ 2 mu} (hu : E.IsAffineProjection V b u) (c : ℝ) :
    E.IsAffineProjection V (c • b) (c • u) := by
  refine ⟨E.domain.smul_mem c hu.1, ?_, ?_⟩
  · simpa only [smul_sub] using V.smul_mem c hu.2.1
  · intro w hw
    rw [E.form_smul_left c u hu.1 w (hV hw), hu.2.2 w hw, mul_zero]

/-- Unique affine orthogonal representatives define a linear projection on the form domain. -/
def affineProjection (E : ClosedForm mu) (V : Submodule ℝ (Lp ℝ 2 mu))
    (hV : V ≤ E.domain)
    (hex : ∀ b ∈ E.domain, ∃! u, E.IsAffineProjection V b u) :
    E.domain →ₗ[ℝ] Lp ℝ 2 mu where
  toFun b := Classical.choose (hex b b.property)
  map_add' b c := by
    have hb := (Classical.choose_spec (hex b b.property)).1
    have hc := (Classical.choose_spec (hex c c.property)).1
    exact ((Classical.choose_spec (hex (b + c) (b + c).property)).2 _ (hb.add hV hc)).symm
  map_smul' c b := by
    have hb := (Classical.choose_spec (hex b b.property)).1
    exact ((Classical.choose_spec (hex (c • b) (c • b).property)).2 _ (hb.smul hV c)).symm

/-- The linear projection has the prescribed affine trace and orthogonality. -/
theorem affineProjection_spec (E : ClosedForm mu) (V : Submodule ℝ (Lp ℝ 2 mu))
    (hV : V ≤ E.domain)
    (hex : ∀ b ∈ E.domain, ∃! u, E.IsAffineProjection V b u) (b : E.domain) :
    E.IsAffineProjection V b (E.affineProjection V hV hex b) :=
  (Classical.choose_spec (hex b b.property)).1

end
end SubdiffusiveProcess.DirichletForm.ClosedForm
