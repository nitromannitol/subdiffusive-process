import SubdiffusiveProcess.Probability.ProductConditionalExpectation
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Finite-moment contraction of independent-block averages

Source: `lem:band`, the projection inequality B1. Fiberwise L1-to-Lp norm
comparison and Tonelli prove the finite-p contraction directly. This avoids
requiring a general conditional Jensen theorem. The result is transported by
actual measure-preserving equivalences for use on the layer product.

These statements do not supply quantitative resampling or response compactness.
-/

open MeasureTheory
open scoped MeasureTheory ENNReal

namespace SubdiffusiveProcess

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The norm of a probability average is bounded by every Lp norm, p ≥ 1. -/
theorem enorm_integral_le_eLpNorm {p : ℝ≥0∞} (hp : 1 ≤ p) {f : A → ℝ}
    (hf : AEStronglyMeasurable f μ) : ‖∫ a, f a ∂μ‖ₑ ≤ eLpNorm f p μ := by
  calc
    ‖∫ a, f a ∂μ‖ₑ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm f 1 μ := (eLpNorm_one_eq_lintegral_enorm).symm
    _ ≤ eLpNorm f p μ := eLpNorm_le_eLpNorm_of_exponent_le hp hf

omit [IsProbabilityMeasure μ] in
/-- Integrating out a probability coordinate contracts every finite Lp seminorm. -/
theorem eLpNorm_prod_integral_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : A × B → ℝ} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    eLpNorm (fun x : A × B => ∫ b, f (x.1, b) ∂ν) p (μ.prod ν) ≤
      eLpNorm f p (μ.prod ν) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hmean := hf.integral_prod_right'
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hp_top,
    eLpNorm_eq_lintegral_rpow_enorm hp0 hp_top]
  apply ENNReal.rpow_le_rpow _ (le_of_lt (one_div_pos.mpr hpr))
  rw [lintegral_prod _ (hmean.comp_fst.enorm.pow_const p.toReal),
    lintegral_prod _ (hf.enorm.pow_const p.toReal)]
  simp only [lintegral_const, measure_univ, mul_one]
  apply lintegral_mono_ae
  filter_upwards [hf.prodMk_left] with a ha
  calc
    ‖∫ b, f (a, b) ∂ν‖ₑ ^ p.toReal ≤ (eLpNorm (fun b => f (a, b)) p ν) ^ p.toReal :=
      ENNReal.rpow_le_rpow (enorm_integral_le_eLpNorm hp ha) hpr.le
    _ = ∫⁻ b, ‖f (a, b)‖ₑ ^ p.toReal ∂ν := by
      rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
      exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr).symm

/-- Finite-p contraction for the actual first-coordinate conditional expectation. -/
theorem condExp_prod_fst_eLpNorm_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : A × B → ℝ} (hf : Integrable f (μ.prod ν)) :
    eLpNorm ((μ.prod ν)[f | (inferInstance : MeasurableSpace A).comap Prod.fst])
      p (μ.prod ν) ≤ eLpNorm f p (μ.prod ν) := by
  rw [eLpNorm_congr_ae (condExp_prod_fst_integral hf)]
  exact eLpNorm_prod_integral_le hp hp_top hf.aestronglyMeasurable

variable {C : Type*} [MeasurableSpace C] {τ : Measure C} [IsProbabilityMeasure τ]

/-- B1 for every finite p ≥ 1; extended norms also allow infinite values. -/
theorem product_condExp_error_eLpNorm_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : (A × B) × C → ℝ} (hf : Integrable f ((μ.prod ν).prod τ)) :
    eLpNorm (f - ((μ.prod ν).prod τ)[f | middleSigma]) p ((μ.prod ν).prod τ) ≤
      eLpNorm (f - ((μ.prod ν).prod τ)[f | leftMiddleSigma]) p ((μ.prod ν).prod τ) +
      eLpNorm (f - ((μ.prod ν).prod τ)[f | middleRightSigma]) p ((μ.prod ν).prod τ) := by
  rw [eLpNorm_congr_ae (product_condExp_error_decomposition hf)]
  refine (eLpNorm_add_le
    (hf.sub (integrable_condExp (m := leftMiddleSigma))).aestronglyMeasurable
    integrable_condExp.aestronglyMeasurable hp).trans ?_
  exact add_le_add le_rfl
    (condExp_prod_fst_eLpNorm_le hp hp_top
      (hf.sub (integrable_condExp (m := middleRightSigma))))

/-- Conditional-expectation errors have the same Lp norm after a measure-preserving relabeling. -/
theorem eLpNorm_condExp_error_comp_measurableEquiv {D E : Type*}
    {m : MeasurableSpace E} [mD : MeasurableSpace D] [mE : MeasurableSpace E]
    {ξ : Measure D} {ζ : Measure E} [IsFiniteMeasure ξ] [IsFiniteMeasure ζ]
    (e : D ≃ᵐ E) (he : MeasurePreserving e ξ ζ) (hm : m ≤ mE)
    {f : D → ℝ} (hf : Integrable f ξ) (p : ℝ≥0∞) :
    eLpNorm (f - ξ[f | m.comap e]) p ξ =
      eLpNorm (f ∘ e.symm - ζ[f ∘ e.symm | m]) p ζ := by
  have hg : Integrable (f ∘ e.symm) ζ := (he.symm e).integrable_comp_of_integrable hf
  have hce : ξ[f | m.comap e] =ᵐ[ξ] ζ[f ∘ e.symm | m] ∘ e := by
    simpa only [Function.comp_def, e.symm_apply_apply] using
      condExp_comp_measurableEquiv e he hm hg
  have hdiff : (f - ξ[f | m.comap e]) =ᵐ[ξ]
      (f ∘ e.symm - ζ[f ∘ e.symm | m]) ∘ e := by
    filter_upwards [hce] with x hx
    simp only [Pi.sub_apply, Function.comp_apply, e.symm_apply_apply] at hx ⊢
    rw [hx]
  rw [eLpNorm_congr_ae hdiff]
  exact eLpNorm_comp_measurePreserving (hg.sub integrable_condExp).aestronglyMeasurable he

/-- B1 on any probability space explicitly identified with three independent blocks. -/
theorem product_condExp_error_eLpNorm_equiv_le {D : Type*} [MeasurableSpace D]
    {ξ : Measure D} [IsProbabilityMeasure ξ]
    (e : D ≃ᵐ (A × B) × C) (he : MeasurePreserving e ξ ((μ.prod ν).prod τ))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : D → ℝ} (hf : Integrable f ξ) :
    eLpNorm (f - ξ[f | middleSigma.comap e]) p ξ ≤
      eLpNorm (f - ξ[f | leftMiddleSigma.comap e]) p ξ +
      eLpNorm (f - ξ[f | middleRightSigma.comap e]) p ξ := by
  have hm0 : middleSigma ≤ (inferInstance : MeasurableSpace ((A × B) × C)) :=
    (measurable_snd.comp measurable_fst).comap_le
  have hmAB : leftMiddleSigma ≤ (inferInstance : MeasurableSpace ((A × B) × C)) :=
    measurable_fst.comap_le
  have hmBC : middleRightSigma ≤ (inferInstance : MeasurableSpace ((A × B) × C)) :=
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd).comap_le
  rw [eLpNorm_condExp_error_comp_measurableEquiv e he hm0 hf,
    eLpNorm_condExp_error_comp_measurableEquiv e he hmAB hf,
    eLpNorm_condExp_error_comp_measurableEquiv e he hmBC hf]
  exact product_condExp_error_eLpNorm_le hp hp_top
    ((he.symm e).integrable_comp_of_integrable hf)

end SubdiffusiveProcess
