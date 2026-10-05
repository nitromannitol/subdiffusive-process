module

public import SubdiffusiveProcess.DirichletForm.Energy
public import SubdiffusiveProcess.DirichletForm.ClosedFormProjection

@[expose] public section

/-! Classical orthogonal projection for a coercive closed symmetric form.
This Hilbert-space fact has no coefficient, spatial energy measure, random field, or concentration assertion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory
open scoped Topology
namespace SubdiffusiveProcess.Paper

/-- An energy-closed variation space admits a unique affine energy-orthogonal representative. -/
theorem inputs_classical_closed_form_projection
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm mu) (V : Submodule ℝ (Lp ℝ 2 mu))
    (_hV : V ≤ E.domain)
    (_hclosed : ∀ (v : ℕ → Lp ℝ 2 mu) (w : Lp ℝ 2 mu),
      (∀ n, v n ∈ V) → w ∈ E.domain →
      Tendsto (fun n => E.energyNormSq (v n - w)) atTop (𝓝 0) → w ∈ V)
    (C : ℝ) (_hC : 0 < C) (_hcoerc : ∀ v ∈ E.domain, ‖v‖ ^ 2 ≤ C * E.form v v)
    (b : Lp ℝ 2 mu) (_hb : b ∈ E.domain) :
    ∃! u : Lp ℝ 2 mu, u ∈ E.domain ∧ u - b ∈ V ∧ ∀ v ∈ V, E.form u v = 0 := by
  exact SubdiffusiveProcess.CoerciveProjection.exists_unique_energy_orthogonal E V _hV _hclosed C _hC
    _hcoerc b _hb

end SubdiffusiveProcess.Paper
