import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Uniform infrared multiplier moments

The anchored infrared field has exponential-supremum moments with constants
chosen before the model. This supplies a moment bank, not a perturbation bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper
noncomputable section

/-- On a fixed compact set, infrared exponential multipliers have model-independent moments. -/
theorem prop_conc_uniform_infrared_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Compacts (SpatialCoordinates d)) (q : ℝ) (hq : 0 < q) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        MemLp (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  obtain ⟨C, hC, hmoment⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  let B0 : ℝ := 2 * Real.exp (C K * q ^ 2)
  have hB0 : 0 < B0 := mul_pos (by norm_num) (Real.exp_pos _)
  refine ⟨B0 ^ (1 / q), Real.rpow_pos_of_pos hB0 _, ?_⟩
  intro M H hH
  let S : BilateralField d → ℝ := fun om => ‖(H om).restrict (K : Set (SpatialCoordinates d))‖
  have hm : Measurable S :=
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).norm.measurable.comp hH.1
  obtain ⟨hInt, hI⟩ := hmoment M H hH K q hq.le
  have hdelta : M.delta ^ 2 ≤ 1 := by
    have h0 := M.shellPrefix.delta_pos
    have h1 := M.shellPrefix.delta_le_half
    nlinarith only [h0, h1]
  have hbound : (∫ om, Real.exp (q * S om) ∂(chaosSampleLaw M).toMeasure) ≤ B0 := by
    refine hI.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right (mul_nonneg (hC K) (sq_nonneg q)) hdelta
  have hlin : (∫⁻ om, ENNReal.ofReal (Real.exp (q * S om)) ∂(chaosSampleLaw M).toMeasure) ≤
      ENNReal.ofReal B0 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hbound
  have hnorm : eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal q)
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (B0 ^ (1 / q)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.mpr hq).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le,
      ← ENNReal.ofReal_rpow_of_nonneg hB0.le (by positivity)]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    have heq (om : BilateralField d) : ‖Real.exp (S om)‖ₑ ^ q =
        ENNReal.ofReal (Real.exp (q * S om)) := by
      rw [Real.enorm_of_nonneg (Real.exp_pos _).le,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq.le, ← Real.exp_mul, mul_comm]
    simpa only [heq] using hlin
  exact ⟨⟨hm.exp.aestronglyMeasurable, hnorm.trans_lt ENNReal.ofReal_lt_top⟩, hnorm⟩

end
end Paper
