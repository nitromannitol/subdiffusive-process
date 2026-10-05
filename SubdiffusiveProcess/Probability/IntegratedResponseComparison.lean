module

public import SubdiffusiveProcess.Probability.ProductLpContraction
public import SubdiffusiveProcess.Probability.ResponseContinuity

@[expose] public section

/-! # Actual averages of multiplicatively continuous responses

Fubini supplies one integrable fiber. The deterministic comparison then
proves integrability on every fiber before the integral representative is
used. No version of conditional expectation is evaluated at an exceptional
conditioning value. The product formula identifies the resulting continuous
function with the actual conditional expectation almost everywhere.
-/

open MeasureTheory Filter Set
open scoped ENNReal MeasureTheory
namespace SubdiffusiveProcess
variable {X Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- One integrable product response and comparison imply integrability at every retained value. -/
theorem integrable_response_fiber_of_comparison {f : X × Y → ℝ}
    (hm : Measurable f) (hf : Integrable f (μ.prod ν))
    (hn : ∀ x y, 0 ≤ f (x, y)) {C : ℝ}
    (hc : ∀ x x' y, f (x, y) ≤ Real.exp (C * dist x x') * f (x', y)) (x : X) :
    Integrable (fun y => f (x, y)) ν := by
  obtain ⟨x', hx'⟩ := hf.prod_right_ae.exists
  apply (hx'.const_mul (Real.exp (C * dist x x'))).mono'
    (hm.comp measurable_prodMk_left).aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hn x y)] using hc x x' y

/-- Averaging the discarded coordinate preserves the same multiplicative comparison. -/
theorem integrated_response_comparison {f : X × Y → ℝ}
    (hm : Measurable f) (hf : Integrable f (μ.prod ν))
    (hn : ∀ x y, 0 ≤ f (x, y)) {C : ℝ}
    (hc : ∀ x x' y, f (x, y) ≤ Real.exp (C * dist x x') * f (x', y)) (x x' : X) :
    (∫ y, f (x, y) ∂ν) ≤ Real.exp (C * dist x x') * ∫ y, f (x', y) ∂ν := by
  rw [← integral_const_mul]
  exact integral_mono
    (integrable_response_fiber_of_comparison hm hf hn hc x)
    ((integrable_response_fiber_of_comparison hm hf hn hc x').const_mul _)
    (hc x x')

/-- The integral representative is continuous, not merely an almost-everywhere scalar version. -/
theorem continuous_integrated_response {f : X × Y → ℝ}
    (hm : Measurable f) (hf : Integrable f (μ.prod ν))
    (hn : ∀ x y, 0 ≤ f (x, y)) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ x x' y, f (x, y) ≤ Real.exp (C * dist x x') * f (x', y)) :
    Continuous (fun x => ∫ y, f (x, y) ∂ν) := by
  have he := equicontinuous_of_exp_comparison
    (f := fun _ : Unit => fun x => ∫ y, f (x, y) ∂ν) hC
    (fun _ x => integral_nonneg (hn x))
    (fun _ x x' => integrated_response_comparison hm hf hn hc x x')
    (fun x => ⟨∫ y, f (x, y) ∂ν, fun _ => le_rfl⟩)
  exact he.continuous ()

/-- The continuous integral function is an actual first-coordinate conditional expectation. -/
theorem continuous_condExp_response_version {f : X × Y → ℝ}
    (hm : Measurable f) (hf : Integrable f (μ.prod ν))
    (hn : ∀ x y, 0 ≤ f (x, y)) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ x x' y, f (x, y) ≤ Real.exp (C * dist x x') * f (x', y)) :
    Continuous (fun x => ∫ y, f (x, y) ∂ν) ∧
      (μ.prod ν)[f | (inferInstance : MeasurableSpace X).comap Prod.fst] =ᵐ[μ.prod ν]
        fun p => ∫ y, f (p.1, y) ∂ν :=
  ⟨continuous_integrated_response hm hf hn hC hc, condExp_prod_fst_integral hf⟩

end SubdiffusiveProcess
