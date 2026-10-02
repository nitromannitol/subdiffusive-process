import SubdiffusiveProcess.Section6SumErrors.UniformRows
import SubdiffusiveProcess.Assumptions.OGammaBridge

/-!
# MomentBridge

Conversion from a weak Gaussian tail of an almost-everywhere measurable carrier to the expectation-form Gaussian bound.
-/

namespace SubdiffusiveProcess.Section6SumErrors
open MeasureTheory Homogenization IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal BigOperators
noncomputable section

/-- The expectation-form Gaussian bound, allowing an almost-everywhere measurable carrier. -/
theorem lintegral_exp_square_le_of_isBigO {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {A : ℝ}
    (hA : 0 < A) (hm : AEMeasurable X μ) (hX : IsBigO μ (gammaSigma 2) X A) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (((2 * A)⁻¹ * max (X ω) 0) ^ (2 : ℕ))) ∂μ ≤ 2 := by
  let Y := hm.mk X
  have hY : IsBigO μ (gammaSigma 2) Y A := by
    rw [isBigO_gammaSigma_iff] at hX ⊢
    intro t ht
    have hset : absTailEvent Y (A * t) =ᵐ[μ] absTailEvent X (A * t) := by
      filter_upwards [hm.ae_eq_mk] with ω hω
      change (A * t < |hm.mk X ω|) = (A * t < |X ω|)
      rw [← hω]
    have heq := measure_congr hset
    simpa only [Measure.real, heq] using hX ht
  have hG := SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma (by norm_num : (0 : ℝ) < 2)
    hA hm.measurable_mk hY
  have hs : (4 : ℝ) ^ (2 : ℝ)⁻¹ = 2 := by
    norm_num [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [hs] at hG
  have hlin := ofReal_integral_eq_lintegral_ofReal hG.1
    (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))
  have hbound : ∫⁻ ω, ENNReal.ofReal
      (Real.exp (((2 * A)⁻¹ * max (Y ω) 0) ^ (2 : ℕ))) ∂μ ≤ 2 := by
    simp only [Real.rpow_two] at hlin
    rw [← hlin]
    simpa only [Real.rpow_two, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hG.2
  apply le_trans _ hbound
  apply le_of_eq
  apply lintegral_congr_ae
  filter_upwards [hm.ae_eq_mk] with ω hω
  simp only [Y]
  rw [hω]

end
end SubdiffusiveProcess.Section6SumErrors
