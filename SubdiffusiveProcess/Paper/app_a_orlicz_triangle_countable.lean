module

public import SubdiffusiveProcess.Paper.app_a_orlicz_triangle_finite
public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaToolkit
public import SubdiffusiveProcess.Probability.Orlicz.CountableTriangle

@[expose] public section

/-!
Unlabelled claim (paper l.11166, first sentence, Appendix A): "The same conclusion [as `e.orlicz.triangle.inequality`] holds for a countable
family of nonnegative `X_k` with `∑_k a_k < ∞`, by monotone convergence."  `σ ≥ 1`, `X_k ≥ 0` random variables with `X_k ≤ O_{Γ_σ}(a_k)`, `a_k > 0`,
`∑ a_k < ∞` give `∑_k X_k ≤ O_{Γ_σ}(∑_k a_k)`.  The conclusion also asserts almost-sure summability (the real `tsum` is junk `0` off the summable set; the
expectation convention forces `∑ X_k < ∞` a.s., and that is part of what "the sum is `≤ O(…)`" means).
-/

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Triangle inequality, countable nonnegative families**: `σ ≥ 1`, `0 ≤ X_k ≤ O_{Γ_σ}(a_k)`, `a_k > 0`, `∑ a_k < ∞` imply that `∑_k X_k`
converges a.s. and `∑_k X_k ≤ O_{Γ_σ}(∑_k a_k)`. -/
theorem app_a_orlicz_triangle_countable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {σ : ℝ} (hσ : 1 ≤ σ) {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hX0 : ∀ k ω, 0 ≤ X k ω) (ha : ∀ k, 0 < a k) (hasum : Summable a)
    (hXm : ∀ k, AEMeasurable (X k) μ)
    (hX : ∀ k, SubdiffusiveProcess.OGammaLE μ σ (a k) (X k)) :
    (∀ᵐ ω ∂μ, Summable fun k => X k ω) ∧
      SubdiffusiveProcess.OGammaLE μ σ (∑' k, a k) (fun ω => ∑' k, X k ω) := by
  exact SubdiffusiveProcess.Probability.Orlicz.ogammaLE_tsum hσ hX0 ha hasum hXm hX

end Paper
