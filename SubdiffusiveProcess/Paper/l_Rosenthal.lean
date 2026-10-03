module

public import Mathlib
public import SubdiffusiveProcess.Rosenthal.Main

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Paper



theorem l_Rosenthal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 1 ≤ N) (p : ℝ) (hp : 2 ≤ p) (X : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hint : ∀ i, Integrable (X i) μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    (∫⁻ ω, ENNReal.ofReal (|∑ i, X i ω| ^ p) ∂μ) ^ (1 / p) ≤
      ENNReal.ofReal (6 * Real.sqrt p) *
          (∑ i, ∫⁻ ω, ENNReal.ofReal ((X i ω) ^ 2) ∂μ) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (4 * p) *
          (∫⁻ ω, (⨆ i, ENNReal.ofReal |X i ω|) ^ p ∂μ) ^ (1 / p) := by
  have _ := hint
  exact SubdiffusiveProcess.Rosenthal.rosenthal_main μ hN p hp X hmeas hind hmean

end Paper
