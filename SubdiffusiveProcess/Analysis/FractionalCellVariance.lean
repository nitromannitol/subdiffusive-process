import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The square of the extended L2 norm is the integral of the pointwise square. -/
theorem eLpNorm_two_sq_eq_lintegral_sq {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f : X → ℝ) :
    eLpNorm f 2 mu ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂mu := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- Jensen's inequality for averaging against any positive finite measure. -/
theorem sq_sub_mean_le_lintegral_sq {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (hmu : mu univ ≠ 0)
    (f : X → ℝ) (hf : MemLp f 2 mu) (x : X) :
    ENNReal.ofReal ((f x - (mu.real univ)⁻¹ * ∫ y, f y ∂mu) ^ 2) ≤
      (mu univ)⁻¹ * ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂mu := by
  let nu : Measure X := (mu univ)⁻¹ • mu
  have hmut : mu univ ≠ ⊤ := measure_ne_top mu univ
  haveI : IsProbabilityMeasure nu := ⟨by
    dsimp [nu]
    exact ENNReal.inv_mul_cancel hmu hmut⟩
  have hfnu : MemLp f 2 nu := hf.smul_measure (ENNReal.inv_ne_top.mpr hmu)
  have hmean : ∫ y, f y ∂nu = (mu.real univ)⁻¹ * ∫ y, f y ∂mu := by
    rw [integral_smul_measure, ENNReal.toReal_inv]
    rfl
  have hdiff : f x - ∫ y, f y ∂nu = ∫ y, (f x - f y) ∂nu := by
    rw [integral_sub (integrable_const _) (hfnu.integrable (by norm_num)),
      integral_const, probReal_univ, one_smul]
  have hle : ‖∫ y, (f x - f y) ∂nu‖ₑ ≤ eLpNorm (fun y => f x - f y) 2 nu := by
    calc
      ‖∫ y, (f x - f y) ∂nu‖ₑ ≤ ∫⁻ y, ‖f x - f y‖ₑ ∂nu :=
        enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun y => f x - f y) 1 nu :=
        eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm (fun y => f x - f y) 2 nu :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
          (aestronglyMeasurable_const.sub hfnu.aestronglyMeasurable)
  calc
    ENNReal.ofReal ((f x - (mu.real univ)⁻¹ * ∫ y, f y ∂mu) ^ 2) =
        ‖∫ y, (f x - f y) ∂nu‖ₑ ^ 2 := by
      rw [← hdiff, hmean, Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    _ ≤ eLpNorm (fun y => f x - f y) 2 nu ^ 2 := pow_le_pow_left₀ (zero_le _) hle 2
    _ = ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂nu :=
      eLpNorm_two_sq_eq_lintegral_sq _ _
    _ = (mu univ)⁻¹ * ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂mu :=
      lintegral_smul_measure _ _

end SubdiffusiveProcess
