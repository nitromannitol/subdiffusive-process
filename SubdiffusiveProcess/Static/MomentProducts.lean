module

public import SubdiffusiveProcess.Static.SubscaleCubeMoments

@[expose] public section

/-! # Moment products with an explicit geometric factor -/
open MeasureTheory SubdiffusiveProcess.Static
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The equal-order Holder product preserves the geometric exponent. -/
theorem moment_le_of_product_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f F g : Ω → ℝ) (hF : Measurable F) (hg : Measurable g)
    (hf0 : ∀ ω, 0 ≤ f ω) (hF0 : ∀ ω, 0 ≤ F ω) (hg0 : ∀ ω, 0 ≤ g ω)
    {q B A T : ℝ} (hq : 0 < q) (hB : 0 ≤ B) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hfg : ∀ ω, f ω ≤ F ω * g ω)
    (hFM : (∫⁻ ω, ENNReal.ofReal (F ω ^ (2 * q)) ∂μ) ≤
      ENNReal.ofReal ((B * T) ^ (2 * q)))
    (hgM : (∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * q)) ∂μ) ≤ ENNReal.ofReal A) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂μ) ≤
      ENNReal.ofReal ((B ^ (2 * q) * A) ^ (1 / 2 : ℝ) * T ^ q) := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((F ω * g ω) ^ q) ∂μ :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (hf0 ω) (hfg ω) hq.le)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (F ω ^ (2 * q)) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * q)) ∂μ) ^ (1 / 2 : ℝ) :=
      product_moment_le _ hF hg hF0 hg0 q
    _ ≤ ENNReal.ofReal ((B * T) ^ (2 * q)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal A ^ (1 / 2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hFM (by norm_num))
        (ENNReal.rpow_le_rpow hgM (by norm_num))
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hA (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← Real.rpow_mul (mul_nonneg hB hT),
        show (2 * q) * (1 / 2 : ℝ) = q by ring,
        Real.mul_rpow hB hT, Real.mul_rpow (by positivity) hA,
        ← Real.rpow_mul hB, show (2 * q) * (1 / 2 : ℝ) = q by ring]
      ring

/-- A real nonnegative moment bound gives an `Lᵖ` bound with its exact root. -/
theorem eLpNorm_le_of_moment_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (h : (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂μ) ≤ ENNReal.ofReal C) :
    SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C ^ q⁻¹) := by
  have hr := ENNReal.rpow_le_rpow h (inv_nonneg.mpr hq.le)
  rw [lintegral_rpow_eq_eLpNorm_rpow μ f hf hq, ← ENNReal.rpow_mul,
    mul_inv_cancel₀ hq.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hC (inv_nonneg.mpr hq.le)] at hr
  exact hr

end SubdiffusiveProcess.Static
