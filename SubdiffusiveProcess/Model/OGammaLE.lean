module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Stretched-exponential moment control

`OGammaLE μ σ A X` specifies integrability and an expectation at most two
for `exp ((A⁻¹ max X 0)^σ)`. The paper's probability interpretation uses
`μ` a probability measure and `σ > 0`, `A > 0`. The predicate remains defined
for other measures and parameters using Lean's total inverse and real power.
Its integrability conjunct is part of the definition; a bound on a totalized
real integral alone would not supply it. `SubdiffusiveProcess.Assumptions.OGammaBridge` gives
its probability-tail comparison under the corresponding domain hypotheses.
-/

open MeasureTheory

/-- The expectation convention for `X ≤ O_{Γ_σ}(A)` used in Appendix A. -/

def SubdiffusiveProcess.OGammaLE {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (σ A : ℝ) (X : Ω → ℝ) : Prop :=
  Integrable
      (fun ω ↦ Real.exp ((A⁻¹ * max (X ω) 0) ^ σ)) μ ∧
    ∫ ω, Real.exp ((A⁻¹ * max (X ω) 0) ^ σ) ∂μ ≤ 2

