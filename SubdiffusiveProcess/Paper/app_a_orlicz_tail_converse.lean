module

public import SubdiffusiveProcess.Paper.app_a_orlicz_tail_bound
public import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
public import SubdiffusiveProcess.Probability.Orlicz.TailConverse

@[expose] public section

/-!
Unlabelled claim (paper l.11157, Appendix A; cited from the converse part of AKM Lemma A.1): if `P[X ≥ t A] ≤ exp(−t^σ)` for every
`t ≥ 0`, then `X ≤ O_{Γ_σ}(2^{1/σ} A)` (expectation convention, `SubdiffusiveProcess.OGammaLE`).  `X` is a random variable (a.e.-measurable).
The constant `2^{1/σ}` is exact: `E exp((X₊/(2^{1/σ}A))^σ) ≤ 2` by the layer-cake formula.
-/

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Converse of the tail bound**: `P[X ≥ tA] ≤ exp(−t^σ)` for all `t ≥ 0` implies `X ≤ O_{Γ_σ}(2^{1/σ} A)`. -/
theorem app_a_orlicz_tail_converse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    (hX : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t * A ≤ X ω} ≤ Real.exp (-(t ^ σ))) :
    SubdiffusiveProcess.OGammaLE μ σ (2 ^ (1 / σ) * A) X := by
  exact SubdiffusiveProcess.Probability.Orlicz.ogammaLE_of_all_level_tail hσ hA hXm hX

end Paper
