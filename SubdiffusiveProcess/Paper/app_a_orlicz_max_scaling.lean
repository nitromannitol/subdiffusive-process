import SubdiffusiveProcess.Paper.app_a_orlicz_tail_bound
import SubdiffusiveProcess.Paper.app_a_orlicz_tail_converse
import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSup
import SubdiffusiveProcess.Probability.Orlicz.Maximum

/-!
Unlabelled claim (paper l.11166-11172, Appendix A), equation `e.max.scaling.O.Gamma.Two`: for every `s > 0` there is `C_s` (depending only on `s`)
such that for every `σ > 0`, `k ≥ 1` and random variables `X_1, …, X_k` with `X_i ≤ O_{Γ_s}(σ)`, `max_i X_i ≤ O_{Γ_s}(C_s (log 2k)^{1/s} σ)`.
Here `σ` is the SCALE (as in the paper) and `s` the exponent.  The index set is a nonempty `Finset` `I` with `k = I.card`; `C` is chosen before `Ω`, `μ`,
`σ`, `I`, `X` (it depends only on `s`); `Ω`, `ι : Type`.  The `X_i` are random variables (measurable).
-/

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Maximum scaling `(e.max.scaling.O.Gamma.Two)`**: `X_i ≤ O_{Γ_s}(σ)` for `i ∈ I` imply
`max_{i∈I} X_i ≤ O_{Γ_s}(C_s (log(2|I|))^{1/s} σ)`, with `C_s` depending only on `s`. -/
theorem app_a_orlicz_max_scaling (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
        ∀ σ : ℝ, 0 < σ → ∀ (ι : Type) (I : Finset ι) (hI : I.Nonempty) (X : ι → Ω → ℝ),
          (∀ i ∈ I, Measurable (X i)) → (∀ i ∈ I, SubdiffusiveProcess.OGammaLE μ s σ (X i)) →
          SubdiffusiveProcess.OGammaLE μ s (C * (Real.log (2 * (I.card : ℝ))) ^ (1 / s) * σ)
            (fun ω => I.sup' hI (fun i => X i ω)) := by
  exact SubdiffusiveProcess.Probability.Orlicz.exists_ogammaLE_maximum s hs

end Paper
