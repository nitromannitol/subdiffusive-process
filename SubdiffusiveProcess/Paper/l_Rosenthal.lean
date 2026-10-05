module

public import Mathlib
public import SubdiffusiveProcess.Rosenthal.Main

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Paper

/-- **Lemma `l.Rosenthal`** (Rosenthal's inequality).

Proved with the paper's constants: for `p ∈ [2,∞)`, `N ∈ ℕ` and independent `X_1,…,X_N` with `E X_i = 0`,
`E[|Σ X_i|^p]^{1/p} ≤ 6 p^{1/2} (Σ E[X_i²])^{1/2} + 4 p E[max_i |X_i|^p]^{1/p}`.
All expectations are taken in `[0,∞]` (lower integrals `∫⁻`), so the statement is literal also when a moment is infinite.
Proof (`SubdiffusiveProcess.Rosenthal`): library symmetrization to independent differences, Khintchine's inequality for
symmetric independent families (constant `K_s = (2 e^{-s/2} s^{s/2})^{1/s}`), Minkowski for the square function, and the
bound `T ≤ Σ E X_i² + 2 K_{p/2} ‖max|X_i|‖_p T^{1/2}` for `T = ‖Σ X_i²‖_{p/2}`; then `2 K_p ≤ 6 √p`, `4 K_p K_{p/2} ≤ 4 p`. -/
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

end SubdiffusiveProcess.Paper
