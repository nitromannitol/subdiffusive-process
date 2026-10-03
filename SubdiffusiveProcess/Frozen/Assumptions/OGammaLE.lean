module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Expectation-form stretched-exponential control
-/

open MeasureTheory




def SubdiffusiveProcess.OGammaLE {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (σ A : ℝ) (X : Ω → ℝ) : Prop :=
  Integrable
      (fun ω ↦ Real.exp ((A⁻¹ * max (X ω) 0) ^ σ)) μ ∧
    ∫ ω, Real.exp ((A⁻¹ * max (X ω) 0) ^ σ) ∂μ ≤ 2

