module

public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaToolkit

@[expose] public section

/-!
Unlabelled claim (Appendix A; cited from AKM Lemma A.1), equation `e.orlicz.tail.bound`: if `X ≤ O_{Γ_σ}(A)`
(expectation convention, `SubdiffusiveProcess.OGammaLE μ σ A X`), then `P[X ≥ t A] ≤ 2 exp(−t^σ)` for all `t ≥ 0`.
Follows from the existing `SubdiffusiveProcess.CoarseGrainingVocab.OGamma.measureReal_ge_le_of_ogammaLE`.
-/

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Tail bound `(e.orlicz.tail.bound)`**: `X ≤ O_{Γ_σ}(A)` implies `P[X ≥ tA] ≤ 2 exp(−t^σ)` for every `t ≥ 0`
(`σ > 0`, `A > 0`, `X` a random variable on a probability space). -/
theorem app_a_orlicz_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) {X : Ω → ℝ} (hX : SubdiffusiveProcess.OGammaLE μ σ A X) :
    ∀ t : ℝ, 0 ≤ t → μ.real {ω | t * A ≤ X ω} ≤ 2 * Real.exp (-(t ^ σ)) := by
  intro t ht
  have h := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.measureReal_ge_le_of_ogammaLE hX hA hσ.le
    (lam := t * A) (by positivity)
  have hc : A⁻¹ * (t * A) = t := by field_simp
  rw [hc] at h
  exact h

end SubdiffusiveProcess.Paper
