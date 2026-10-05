module

public import SubdiffusiveProcess.Probability.Orlicz.WeakBridge
public import Homogenization.Probability.IndependentSums.GammaSigmaExpRegime.FiniteSums

@[expose] public section

/-! Independent centered Orlicz sums in the exponential regime. -/
open MeasureTheory ProbabilityTheory
noncomputable section
namespace SubdiffusiveProcess.Probability.Orlicz

theorem exists_ogammaLE_independent_sum (s : ℝ) (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
        ∀ σ : ℝ, 0 < σ → ∀ k : ℕ, 1 ≤ k → ∀ X : Fin k → Ω → ℝ,
          (∀ i, Measurable (X i)) → iIndepFun X μ → (∀ i, ∫ ω, X i ω ∂μ = 0) →
          (∀ i, SubdiffusiveProcess.OGammaLE μ s σ (X i) ∧ SubdiffusiveProcess.OGammaLE μ s σ (fun ω => -X i ω)) →
          SubdiffusiveProcess.OGammaLE μ s (C * Real.sqrt (k : ℝ) * σ) (fun ω => ∑ i, X i ω) ∧
            SubdiffusiveProcess.OGammaLE μ s (C * Real.sqrt (k : ℝ) * σ) (fun ω => -∑ i, X i ω) := by
  let D : ℝ := (1 + Real.log 2) ^ s⁻¹
  let E : ℝ := max 1 (Homogenization.IndependentSums.gammaSigmaExpRegimeEndpointConst s)
  let C : ℝ := (4 : ℝ) ^ s⁻¹ * E * (2 * D)
  have hs : 0 < s := zero_lt_one.trans hs1
  have hD : 0 < D := Real.rpow_pos_of_pos (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]) _
  have hE : 0 < E := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C, mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hE) (mul_pos (by norm_num) hD), ?_⟩
  intro Ω _ μ _ σ hσ k hk X hm hind hmean hX
  let K : ℝ := D * (2 * σ)
  have hK : 0 < K := mul_pos hD (mul_pos (by norm_num) hσ)
  have hweak : ∀ i, Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma s) (X i) K := fun i =>
    isBigO_gammaSigma_of_two_sided hs1.le hσ (hm i).aemeasurable (hX i).1 (hX i).2
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hw := Homogenization.IndependentSums.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
    hind hm hne hs1.le hs2 hK (fun i _ => hweak i) (fun i _ => hmean i)
  have hsum : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma s) (fun ω => ∑ i, X i ω)
      (Homogenization.IndependentSums.gammaSigmaExpRegimeEndpointConst s * Real.sqrt (k : ℝ) * K) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hw
  have hw' : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma s) (fun ω => ∑ i, X i ω)
      (E * Real.sqrt (k : ℝ) * K) :=
    hsum.mono_scale (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)) hK.le)
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hB : 0 < E * Real.sqrt (k : ℝ) * K := mul_pos (mul_pos hE (Real.sqrt_pos.mpr hkp)) hK
  have hSm : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum Finset.univ (fun i _ => hm i)
  have hp := SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma hs hB hSm hw'
  have hn := SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma hs hB hSm.neg hw'.neg
  have hscale : (4 : ℝ) ^ s⁻¹ * (E * Real.sqrt (k : ℝ) * K) = C * Real.sqrt (k : ℝ) * σ := by
    dsimp [C, K]
    ring
  exact ⟨by simpa only [hscale] using hp, by simpa only [hscale, Pi.neg_def] using hn⟩

end SubdiffusiveProcess.Probability.Orlicz
