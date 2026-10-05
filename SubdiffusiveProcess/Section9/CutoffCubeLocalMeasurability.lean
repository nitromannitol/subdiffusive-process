
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section




namespace SubdiffusiveProcess.Section9

open MeasureTheory

noncomputable section

/-- A spatially continuous, samplewise measurable integrand has a measurable
integral. -/
theorem measurable_integral_of_continuous_of_measurable
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [MetricSpace E] [SecondCountableTopology E]
    [BorelSpace E] (mu : Measure E) [SFinite mu] (f : Omega → E → ℝ)
    (hcont : ∀ omega, Continuous (f omega))
    (hmeas : ∀ x, Measurable (fun omega ↦ f omega x)) :
    Measurable (fun omega ↦ ∫ x, f omega x ∂mu) := by
  have hjoint' : Measurable (fun z : E × Omega ↦ f z.2 z.1) := by
    exact measurable_uncurry_of_continuous_of_measurable
      (u := fun (x : E) (omega : Omega) ↦ f omega x) hcont hmeas
  have hjoint : Measurable (fun z : Omega × E ↦ f z.1 z.2) :=
    hjoint'.comp measurable_swap
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

end


end SubdiffusiveProcess.Section9
