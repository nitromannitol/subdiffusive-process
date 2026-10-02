import SubdiffusiveProcess.DirichletForm.All
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



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

end Paper
