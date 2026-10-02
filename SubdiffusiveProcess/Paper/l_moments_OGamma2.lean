import Mathlib
import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
import SubdiffusiveProcess.Probability.OGammaTwoMoments
import SubdiffusiveProcess.Probability.OGammaTwoExponential




open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

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

end Paper
