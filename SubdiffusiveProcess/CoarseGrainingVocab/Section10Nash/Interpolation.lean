import Homogenization.Sobolev.CubeEmbedding.GagliardoNirenbergSobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The `L¹`--`L²`--Sobolev interpolation behind Nash's inequality

This file proves the exact Hölder interpolation used to turn an `L² → L^{2*}`
Sobolev estimate into a Nash estimate.  The proof is measure-theoretic and is
kept separate from the cube geometry in `Cube.lean`.

The exponent is `Homogenization.twoStar d = 2d / (d - 2)`, so this module has
the same `3 ≤ d` range as CoarseGraining's critical cube embedding.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section10Nash

open MeasureTheory Homogenization
open scoped ENNReal NNReal

noncomputable section

/-- Hölder interpolation in integral form, with all exponents displayed.
This is the algebraic core of the critical-exponent Nash inequality. -/
theorem lintegral_nash_interpolation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (d : ℕ) (hd : 3 ≤ d)
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (((d : ℝ) + 2) / 2) ≤
      (∫⁻ x, ‖f x‖ₑ ∂μ) ^ (2 : ℝ) *
        (∫⁻ x, ‖f x‖ₑ ^ ((2 : ℝ) * d / (d - 2)) ∂μ) ^
          (((d : ℝ) - 2) / 2) := by
  let q : ℝ := ((d : ℝ) + 2) / 4
  let r : ℝ := ((d : ℝ) + 2) / ((d : ℝ) - 2)
  let F : α → ℝ≥0∞ := fun x => ‖f x‖ₑ ^ (4 / ((d : ℝ) + 2))
  let G : α → ℝ≥0∞ := fun x => ‖f x‖ₑ ^ ((2 * (d : ℝ)) / ((d : ℝ) + 2))
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : (1 : ℝ) < q := by
    dsimp [q]
    linarith
  have hsum : (1 : ℝ) / 1 = 1 / q + 1 / r := by
    dsimp [q, r]
    field_simp
    ring
  have hholder := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr
    (μ := μ) (f := F) (g := G) (p := (1 : ℝ)) (q := q) (r := r)
    zero_lt_one hq hsum (hf.enorm.pow_const _) (hf.enorm.pow_const _)
  have hpow := ENNReal.rpow_le_rpow hholder
    (by positivity : 0 ≤ ((d : ℝ) + 2) / 2)
  dsimp [F, G, q, r] at hpow
  norm_num at hpow
  convert hpow using 1
  · apply congrArg (fun z : ℝ≥0∞ => z ^ (((d : ℝ) + 2) / 2))
    apply lintegral_congr
    intro x
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  · rw [ENNReal.mul_rpow_of_nonneg]
    rotate_left
    · positivity
    simp_rw [← ENNReal.rpow_mul]
    have hAint : 4 / ((d : ℝ) + 2) * (((d : ℝ) + 2) / 4) = 1 := by
      field_simp
    have hAout : 4 / ((d : ℝ) + 2) * (((d : ℝ) + 2) / 2) = 2 := by
      field_simp
      norm_num
    have hBint : 2 * (d : ℝ) / ((d : ℝ) + 2) *
        (((d : ℝ) + 2) / ((d : ℝ) - 2)) = 2 * (d : ℝ) / ((d : ℝ) - 2) := by
      field_simp
    have hBout : ((d : ℝ) - 2) / ((d : ℝ) + 2) *
        (((d : ℝ) + 2) / 2) = ((d : ℝ) - 2) / 2 := by
      field_simp
    rw [hAint, hAout, hBint, hBout]
    simp only [ENNReal.rpow_one]

/-- Critical-exponent interpolation in `eLpNorm` form:
`‖f‖₂^(d+2) ≤ ‖f‖₁² ‖f‖_(2*)^d`. -/
theorem eLpNorm_nash_interpolation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (d : ℕ) (hd : 3 ≤ d)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ (d + 2) ≤
      eLpNorm f 1 μ ^ 2 * eLpNorm f (twoStar d) μ ^ d := by
  have hdle : (2 : ℝ≥0) ≤ (d : ℝ≥0) := by
    exact_mod_cast (by omega : 2 ≤ d)
  have htwoStarReal : (twoStar d : ℝ) = 2 * (d : ℝ) / ((d : ℝ) - 2) := by
    rw [twoStar, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sub hdle]
    push_cast
    rfl
  have h := lintegral_nash_interpolation μ f d hd hf
  calc
    eLpNorm f 2 μ ^ (d + 2) =
        (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (((d : ℝ) + 2) / 2) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      simp only [ENNReal.toReal_ofNat, one_div]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      push_cast
      ring
    _ ≤ (∫⁻ x, ‖f x‖ₑ ∂μ) ^ (2 : ℝ) *
        (∫⁻ x, ‖f x‖ₑ ^ ((2 : ℝ) * d / (d - 2)) ∂μ) ^
          (((d : ℝ) - 2) / 2) := h
    _ = eLpNorm f 1 μ ^ 2 * eLpNorm f (twoStar d) μ ^ d := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
          (by norm_num : (1 : ℝ≥0∞) ≠ ∞),
        eLpNorm_eq_lintegral_rpow_enorm]
      · simp only [one_div]
        rw [show (twoStar d : ℝ≥0∞).toReal = 2 * (d : ℝ) / ((d : ℝ) - 2) by
          simpa using htwoStarReal]
        simp_rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        · norm_num
        · congr 1
          field_simp
      · dsimp [twoStar]
        have ht : (2 * (d : ℝ≥0)) / ((d : ℝ≥0) - 2) ≠ 0 := by
          apply div_ne_zero
          · positivity
          · exact (tsub_pos_iff_lt.mpr (by exact_mod_cast (by omega : 2 < d))).ne'
        exact_mod_cast ht
      · exact ENNReal.coe_ne_top



theorem eLpNorm_two_four_nash_interpolation
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ (3 : ℕ) ≤ eLpNorm f 1 μ * eLpNorm f 4 μ ^ (2 : ℕ) := by
  let F : α → ℝ≥0∞ := fun x => ‖f x‖ₑ ^ (2 / 3 : ℝ)
  let G : α → ℝ≥0∞ := fun x => ‖f x‖ₑ ^ (4 / 3 : ℝ)
  have hholder := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr
    (μ := μ) (f := F) (g := G) (p := (1 : ℝ))
    (q := (3 / 2 : ℝ)) (r := (3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (hf.enorm.pow_const _) (hf.enorm.pow_const _)
  have hpow := ENNReal.rpow_le_rpow hholder (by norm_num : 0 ≤ (3 / 2 : ℝ))
  dsimp [F, G] at hpow
  norm_num at hpow
  calc
    eLpNorm f 2 μ ^ (3 : ℕ) =
        (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (3 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      simp only [ENNReal.toReal_ofNat, one_div]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ (∫⁻ x, ‖f x‖ₑ ∂μ) *
        (∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
      convert hpow using 1
      · apply congrArg (fun z : ℝ≥0∞ => z ^ (3 / 2 : ℝ))
        apply lintegral_congr
        intro x
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
        congr 1
        norm_num
      · rw [ENNReal.mul_rpow_of_nonneg]
        rotate_left
        · positivity
        simp_rw [← ENNReal.rpow_mul]
        norm_num
        congr 2
        apply lintegral_congr
        intro x
        rw [← ENNReal.rpow_natCast ‖f x‖ₑ 4,
          ← ENNReal.rpow_natCast (‖f x‖ₑ ^ (4 / 3 : ℝ)) 3,
          ← ENNReal.rpow_mul]
        norm_num
    _ = eLpNorm f 1 μ * eLpNorm f 4 μ ^ (2 : ℕ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
          (by norm_num : (1 : ℝ≥0∞) ≠ ∞),
        eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (4 : ℝ≥0∞) ≠ 0)
          (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
      simp only [ENNReal.toReal_ofNat, one_div]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section10Nash
