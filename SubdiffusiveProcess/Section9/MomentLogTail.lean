module

public import Mathlib.MeasureTheory.Integral.Bochner.L1

public import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE

@[expose] public section

/-!
# Logarithmic upper tails from a centered moment

This file isolates the deterministic probability calculation used after the
one-cube moment estimate in the proof of the weighted-volume lemma.
-/

open MeasureTheory Set

namespace SubdiffusiveProcess.Section9

/-- Above the cutoff `9 / 8`, the exponential logarithmic observable is
controlled by the centered power moment. -/
private theorem exp_mul_posPart_log_sub_le (x p : ℝ) (hx : 0 ≤ x) (hp : 0 ≤ p) :
    Real.exp (p * max (Real.log x - Real.log (9 / 8 : ℝ)) 0) ≤
      1 + (8 : ℝ) ^ p * |x - 1| ^ p := by
  by_cases hlog : Real.log x - Real.log (9 / 8 : ℝ) ≤ 0
  · rw [max_eq_right hlog]
    simp only [mul_zero, Real.exp_zero]
    exact le_add_of_nonneg_right
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _))
  have hlog_pos : 0 < Real.log x - Real.log (9 / 8 : ℝ) := lt_of_not_ge hlog
  have hx_pos : 0 < x := by
    by_contra hx0
    have : x = 0 := le_antisymm (le_of_not_gt hx0) hx
    rw [this, Real.log_zero, zero_sub] at hlog_pos
    have := Real.log_pos (by norm_num : (1 : ℝ) < 9 / 8)
    linarith
  have hc : 0 < (9 / 8 : ℝ) := by norm_num
  have hratio : 1 < x / (9 / 8 : ℝ) := by
    apply (lt_div_iff₀ hc).2
    have : (9 / 8 : ℝ) < x := (Real.log_lt_log_iff hc hx_pos).mp (by linarith)
    simpa using this
  have hcenter : x / (9 / 8 : ℝ) ≤ 8 * |x - 1| := by
    have hcx : (9 / 8 : ℝ) < x := by
      have := (lt_div_iff₀ hc).mp hratio
      simpa using this
    have hx1 : 1 < x := by linarith
    rw [abs_of_pos (sub_pos.mpr hx1)]
    norm_num
    linarith
  rw [max_eq_left hlog_pos.le]
  have hexp : Real.exp (p * (Real.log x - Real.log (9 / 8 : ℝ))) =
      (x / (9 / 8 : ℝ)) ^ p := by
    rw [Real.rpow_def_of_pos (div_pos hx_pos hc)]
    congr 1
    rw [Real.log_div hx_pos.ne' hc.ne']
    ring
  rw [hexp]
  calc
    (x / (9 / 8 : ℝ)) ^ p ≤ (8 * |x - 1|) ^ p :=
      Real.rpow_le_rpow (div_nonneg hx hc.le) hcenter hp
    _ = (8 : ℝ) ^ p * |x - 1| ^ p := by rw [Real.mul_rpow (by norm_num) (abs_nonneg _)]
    _ ≤ 1 + (8 : ℝ) ^ p * |x - 1| ^ p := by linarith

/-- A small centered `p`-moment gives the source's one-sided logarithmic
`O_{Γ₁}` estimate, with scale `1 / p`. -/
theorem ogammaLE_one_log_sub_of_centered_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ℝ) (p : ℝ)
    (hA : Measurable A) (hA_nonneg : ∀ ω, 0 ≤ A ω) (hp : 2 ≤ p)
    (hmoment : Integrable (fun ω ↦ |A ω - 1| ^ p) μ)
    (hsmall : (8 : ℝ) ^ p * ∫ ω, |A ω - 1| ^ p ∂μ ≤ 1) :
    SubdiffusiveProcess.OGammaLE μ 1 p⁻¹
      (fun ω ↦ Real.log (A ω) - Real.log (9 / 8 : ℝ)) := by
  let X : Ω → ℝ := fun ω ↦
    Real.exp (p * max (Real.log (A ω) - Real.log (9 / 8 : ℝ)) 0)
  let Y : Ω → ℝ := fun ω ↦ 1 + (8 : ℝ) ^ p * |A ω - 1| ^ p
  have hX_meas : Measurable X := by
    fun_prop
  have hY_int : Integrable Y μ := by
    exact (integrable_const 1).add (hmoment.const_mul ((8 : ℝ) ^ p))
  have hXY : ∀ ω, X ω ≤ Y ω := fun ω ↦
    exp_mul_posPart_log_sub_le (A ω) p (hA_nonneg ω) (by linarith)
  have hX_int : Integrable X μ := hY_int.mono' hX_meas.aestronglyMeasurable <|
    Filter.Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hXY ω
  unfold SubdiffusiveProcess.OGammaLE
  have hp_pos : 0 < p := by linarith
  have hinv : (p⁻¹)⁻¹ = p := inv_inv p
  have hform : (fun ω ↦ Real.exp
      (((p⁻¹)⁻¹ * max (Real.log (A ω) - Real.log (9 / 8 : ℝ)) 0) ^ (1 : ℝ))) = X := by
    funext ω
    simp only [hinv, Real.rpow_one]
    rfl
  rw [hform]
  refine ⟨hX_int, (integral_mono hX_int hY_int hXY).trans ?_⟩
  rw [integral_add (integrable_const 1) (hmoment.const_mul ((8 : ℝ) ^ p)),
    integral_const, integral_const_mul]
  simp only [probReal_univ, one_smul]
  linarith

/-- Markov's inequality in the exact centered-event form used for the
one-cube failure probability. -/
theorem centered_moment_failure_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → ℝ) (p : ℝ) (hp : 0 < p)
    (hmoment : Integrable (fun ω ↦ |A ω - 1| ^ p) μ) :
    (1 / 2 : ℝ) ^ p * μ.real {ω | 1 / 2 ≤ |A ω - 1|} ≤
      ∫ ω, |A ω - 1| ^ p ∂μ := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω ↦ |A ω - 1| ^ p)
    (Filter.Eventually.of_forall fun ω ↦ Real.rpow_nonneg (abs_nonneg _) _) hmoment
    ((1 / 2 : ℝ) ^ p)
  rw [show {ω | 1 / 2 ≤ |A ω - 1|} =
      {ω | (1 / 2 : ℝ) ^ p ≤ |A ω - 1| ^ p} by
    ext ω
    change (1 / 2 : ℝ) ≤ |A ω - 1| ↔ (1 / 2 : ℝ) ^ p ≤ |A ω - 1| ^ p
    exact (Real.rpow_le_rpow_iff
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg _) hp).symm]
  exact hmarkov

end SubdiffusiveProcess.Section9
