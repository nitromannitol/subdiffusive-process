module

public import SubdiffusiveProcess.Paper.app_a_orlicz_tail_bound
public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaTail
public import SubdiffusiveProcess.Probability.Orlicz.IndependentSum

@[expose] public section

/-!
Unlabelled claim (paper l.11173-11177, Appendix A; cited from AKM Lemmas A.7 and A.9), equation `e.CLT.scaling.O.Gamma.Two`: for `s ∈ (1,2]`
there is `C_s` (depending only on `s`) such that for every `σ > 0`, `k ≥ 1` and independent, mean-zero random variables `X_1, …, X_k` with `X_i = O_{Γ_s}(σ)`
(two-sided: `X_i ≤ O(σ)` and `−X_i ≤ O(σ)`), `∑_i X_i = O_{Γ_s}(C_s k^{1/2} σ)` (two-sided).  `σ` is the scale and `s` the exponent, as in the paper;
`C` is chosen before `Ω`, `μ`, `σ`, `k`, `X`; `Ω : Type`.  Independence is `iIndepFun` of the family `X : Fin k → Ω → ℝ`.
-/

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Sums of independent mean-zero variables `(e.CLT.scaling.O.Gamma.Two)`**: `s ∈ (1,2]`, `X_i` independent, mean zero, `X_i = O_{Γ_s}(σ)` imply
`∑_{i<k} X_i = O_{Γ_s}(C_s k^{1/2} σ)`, with `C_s` depending only on `s`. -/
theorem app_a_orlicz_clt_scaling (s : ℝ) (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
        ∀ σ : ℝ, 0 < σ → ∀ k : ℕ, 1 ≤ k → ∀ X : Fin k → Ω → ℝ,
          (∀ i, Measurable (X i)) → iIndepFun X μ → (∀ i, ∫ ω, X i ω ∂μ = 0) →
          (∀ i, SubdiffusiveProcess.OGammaLE μ s σ (X i) ∧ SubdiffusiveProcess.OGammaLE μ s σ (fun ω => -X i ω)) →
          SubdiffusiveProcess.OGammaLE μ s (C * Real.sqrt (k : ℝ) * σ) (fun ω => ∑ i, X i ω) ∧
            SubdiffusiveProcess.OGammaLE μ s (C * Real.sqrt (k : ℝ) * σ) (fun ω => -∑ i, X i ω) := by
  exact SubdiffusiveProcess.Probability.Orlicz.exists_ogammaLE_independent_sum s hs1 hs2

end Paper
