module

public import Mathlib
public import SubdiffusiveProcess.Model.OGammaLE
public import SubdiffusiveProcess.Probability.OGammaTwoMoments
public import SubdiffusiveProcess.Probability.OGammaTwoExponential

@[expose] public section

/-!
The unlabelled lemma of Appendix A (`e.moments.OGamma2` and `e.moments.lognormal` and `e.moments.general.lognormal`, "Moments of random variables with log-normal tails"):
for `X = O_{Γ_2}(σ)` (two-sided, in the expectation convention of Appendix A `(A.1)-(A.2)`,
`SubdiffusiveProcess.OGammaLE μ 2 σ X ∧ SubdiffusiveProcess.OGammaLE μ 2 σ (-X)`), the three moment estimates
`(e.moments.OGamma2)`, `(e.moments.lognormal)`, `(e.moments.general.lognormal)` with ONE universal constant `C` (chosen before `σ`, `X`, `k`, `t`, `m`).
Expectations are lower Lebesgue integrals of `ENNReal.ofReal` of the nonnegative integrand, so that no junk value `0` can occur for a
non-integrable variable; the exponents `k, m` are real (`k > 0`, `m ≥ 1`, as in the paper; `m` is not assumed integral).
No measurability hypothesis on `X` is needed: `OGammaLE` (Bochner integrability of `exp((σ⁻¹ X₊)²)` and of `exp((σ⁻¹ (-X)₊)²)`) makes `X`
a.e.-measurable.
-/

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem l_moments_OGamma2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
        ∀ σ : ℝ, 0 < σ → ∀ X : Ω → ℝ,
          SubdiffusiveProcess.OGammaLE μ 2 σ X → SubdiffusiveProcess.OGammaLE μ 2 σ (fun ω => -X ω) →
          (∀ k : ℝ, 0 < k →
            ∫⁻ ω, ENNReal.ofReal (|X ω| ^ k) ∂μ ≤
              ENNReal.ofReal (C * σ ^ k * Real.Gamma (k / 2 + 1))) ∧
          (∀ t : ℝ, 0 < t →
            ∫⁻ ω, ENNReal.ofReal |Real.exp (t * X ω) - (1 + t * X ω)| ∂μ ≤
              ENNReal.ofReal (C * σ ^ 2 * t ^ 2 * Real.exp (C * σ ^ 2 * t ^ 2))) ∧
          (∀ m : ℝ, 1 ≤ m → ∀ t : ℝ, 0 < t →
            ∫⁻ ω, ENNReal.ofReal (|Real.exp (t * X ω) - 1| ^ m) ∂μ ≤
              ENNReal.ofReal ((C * m ^ (1 / 2 : ℝ) * σ * t) ^ m *
                Real.exp (C * (m * σ * t) ^ 2))) := by
  refine ⟨32, by norm_num, ?_⟩
  intro Ω _ μ _ σ hσ X hp hn
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    refine (SubdiffusiveProcess.Probability.lintegral_abs_rpow_le_ogamma_two hσ hp hn hk).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hG := (Real.Gamma_pos_of_pos (by linarith : 0 < k / 2 + 1)).le
    have hs := Real.rpow_nonneg hσ.le k
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 32) hs) hG
  · intro t ht
    exact SubdiffusiveProcess.Probability.lintegral_exp_remainder_le hσ hp hn ht
  · intro m hm t ht
    exact SubdiffusiveProcess.Probability.lintegral_exp_sub_one_rpow_le hσ hp hn hm ht

end SubdiffusiveProcess.Paper
