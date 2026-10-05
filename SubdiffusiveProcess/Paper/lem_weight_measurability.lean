module

public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- lemma `mfd:lem-borel-weights`, measurability clause.

`omega |-> int exp (g omega x) dmu x` is strongly measurable whenever
`(omega, x) |-> g omega x` is.

How it is used (Lean-encoding commentary, kept out  per the
standing rule): it is applied with `mu = Gamma_E(u)`, the energy measure, which
is finite for `u` in the domain and hence `s`-finite, and with
`g omega = -l(omega)` the contribution of one layer.  That is the measurability
clause of the deletion half of `mfd:lem-borel-weights`: it makes the weighted
form `e^{-l} E` measurable in the remaining layers.  `lem_borel_weights`
consumes it through the positive and negative parts of the Jordan decomposition
of the cross measure.

Stated over an arbitrary measurable space rather than the cube, because nothing
in the argument uses the geometry: the paper's instance is the special case
`mu := Gamma.measure u`. -/
theorem lem_weight_measurability {X : Type*} [MeasurableSpace X] {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure X) [SFinite μ] (g : Ω → X → ℝ)
    (hg : StronglyMeasurable (Function.uncurry g)) :
    StronglyMeasurable fun ω => ∫ x, Real.exp (g ω x) ∂μ := by
  have huc : (Function.uncurry fun (ω : Ω) (x : X) => Real.exp (g ω x))
      = fun p => Real.exp (Function.uncurry g p) := rfl
  have h : StronglyMeasurable
      (Function.uncurry fun (ω : Ω) (x : X) => Real.exp (g ω x)) := by
    rw [huc]
    exact Real.continuous_exp.comp_stronglyMeasurable hg
  exact MeasureTheory.StronglyMeasurable.integral_prod_right h

end SubdiffusiveProcess.Paper
