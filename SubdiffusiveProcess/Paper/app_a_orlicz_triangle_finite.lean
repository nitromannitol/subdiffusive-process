module

public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaToolkit
public import SubdiffusiveProcess.Probability.Orlicz.FiniteTriangle

@[expose] public section

/-!
Unlabelled claim (Appendix A; cited from AKM Lemma A.4), equation `e.orlicz.triangle.inequality`:
for `σ ≥ 1`, a finite index set `I` and random variables `X_k ≤ O_{Γ_σ}(a_k)` (`k ∈ I`, `a_k > 0`), `∑_{k∈I} X_k ≤ O_{Γ_σ}(∑_{k∈I} a_k)`.
Random variables are (a.e.-)measurable: measurability is needed (only `X₊` is controlled by `OGammaLE`, so `(∑ X_k)₊` is not determined by the `(X_k)₊`).
The index set is nonempty (the definition of `O_{Γ_σ}(A)` needs `A > 0`).
-/

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Triangle inequality `(e.orlicz.triangle.inequality)`**, finite index set: `σ ≥ 1`, `X_k ≤ O_{Γ_σ}(a_k)` for `k ∈ I` imply
`∑_{k∈I} X_k ≤ O_{Γ_σ}(∑_{k∈I} a_k)`. -/
theorem app_a_orlicz_triangle_finite {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {σ : ℝ} (hσ : 1 ≤ σ) {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    {X : ι → Ω → ℝ} {a : ι → ℝ} (ha : ∀ k ∈ I, 0 < a k)
    (hXm : ∀ k ∈ I, AEMeasurable (X k) μ)
    (hX : ∀ k ∈ I, SubdiffusiveProcess.OGammaLE μ σ (a k) (X k)) :
    SubdiffusiveProcess.OGammaLE μ σ (∑ k ∈ I, a k) (fun ω => ∑ k ∈ I, X k ω) := by
  exact SubdiffusiveProcess.Probability.Orlicz.ogammaLE_finset_sum hσ I hI ha hXm hX

end SubdiffusiveProcess.Paper
