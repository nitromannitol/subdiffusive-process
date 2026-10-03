module

public import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE

@[expose] public section

/-!
Definition (unlabelled, paper l.11132-11150, Appendix A "Moments of random variables with log-normal tails"): `Γ_σ(t) = exp(t^σ)`,
the relation `X ≤ O_{Γ_σ}(A) :⇔ E[exp((A⁻¹ X₊)^σ)] ≤ 2` (`X₊ = X ∨ 0`) and the two-sided relation `X = O_{Γ_σ}(A) :⇔ X ≤ O(A) ∧ −X ≤ O(A)`
(`e.orlicz.two.sided.definition`), in the convention of AKM Appendix A (A.1)-(A.2), p.416.

It is a THIN definition over the frozen predicate `SubdiffusiveProcess.OGammaLE μ σ A X` (`Integrable (exp((A⁻¹ X₊)^σ)) ∧ ∫ ≤ 2`; the integrability is
what makes the Bochner integral a real expectation).  The principal returns the pair `(X ≤ O(A), X = O(A))`; the auxiliary lemmas unfold it
to the paper's displays.  Hypotheses `σ > 0`, `A > 0` of the paper's definition are left to the users of the relation, as for
`SubdiffusiveProcess.OGammaLE` itself.
-/

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The Orlicz function `Γ_σ(t) = exp(t^σ)` of the paper (`Γ_σ : [0,∞) → [1,∞)`). -/
def aux_app_a_orlicz_notation_Gamma (σ t : ℝ) : ℝ := Real.exp (t ^ σ)

/-- **The Orlicz notation of Appendix A**: for a random variable `X` on `(Ω, μ)`, `σ > 0` and `A > 0`, the pair
`(X ≤ O_{Γ_σ}(A), X = O_{Γ_σ}(A))`, with `X ≤ O_{Γ_σ}(A)` iff `E[exp((A⁻¹ X₊)^σ)] ≤ 2` and `X = O_{Γ_σ}(A)` iff
`X ≤ O_{Γ_σ}(A)` and `−X ≤ O_{Γ_σ}(A)`. -/
def app_a_orlicz_notation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (σ A : ℝ) (X : Ω → ℝ) : Prop × Prop :=
  (SubdiffusiveProcess.OGammaLE μ σ A X, SubdiffusiveProcess.OGammaLE μ σ A X ∧ SubdiffusiveProcess.OGammaLE μ σ A (fun ω => -X ω))

/-- `X ≤ O_{Γ_σ}(A)`: `E[Γ_σ(A⁻¹ X₊)] ≤ 2` (the integrand is integrable). -/
theorem aux_app_a_orlicz_notation_le_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (σ A : ℝ) (X : Ω → ℝ) :
    (app_a_orlicz_notation μ σ A X).1 ↔
      Integrable (fun ω => aux_app_a_orlicz_notation_Gamma σ (A⁻¹ * max (X ω) 0)) μ ∧
        ∫ ω, aux_app_a_orlicz_notation_Gamma σ (A⁻¹ * max (X ω) 0) ∂μ ≤ 2 :=
  Iff.rfl

/-- `X = O_{Γ_σ}(A)`: both `E[Γ_σ(A⁻¹ X₊)] ≤ 2` and `E[Γ_σ(A⁻¹ (−X)₊)] ≤ 2`. -/
theorem aux_app_a_orlicz_notation_eq_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (σ A : ℝ) (X : Ω → ℝ) :
    (app_a_orlicz_notation μ σ A X).2 ↔
      (Integrable (fun ω => aux_app_a_orlicz_notation_Gamma σ (A⁻¹ * max (X ω) 0)) μ ∧
        ∫ ω, aux_app_a_orlicz_notation_Gamma σ (A⁻¹ * max (X ω) 0) ∂μ ≤ 2) ∧
      (Integrable (fun ω => aux_app_a_orlicz_notation_Gamma σ (A⁻¹ * max (-X ω) 0)) μ ∧
        ∫ ω, aux_app_a_orlicz_notation_Gamma σ (A⁻¹ * max (-X ω) 0) ∂μ ≤ 2) :=
  Iff.rfl

/-- `Γ_σ` takes values in `[1, ∞)` on `[0, ∞)`. -/
theorem aux_app_a_orlicz_notation_one_le (σ t : ℝ) (ht : 0 ≤ t) : 1 ≤ aux_app_a_orlicz_notation_Gamma σ t :=
  Real.one_le_exp (Real.rpow_nonneg ht σ)

end Paper
