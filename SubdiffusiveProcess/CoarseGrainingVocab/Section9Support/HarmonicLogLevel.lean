module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicLogPoincare

@[expose] public section

/-!
# From logarithmic square control to a small positive part

A direct pointwise comparison with the absolute logarithm replaces the
equivalent Chebyshev estimate on the small-value set. It introduces no
measurability requirement on the values outside the solution domain.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The positive part below a small threshold is controlled by the
absolute regularized logarithm. -/
theorem harmonic_positive_part_le_scaled_log {t delta T : ℝ}
    (ht : 0 ≤ t) (hdelta : 0 < delta) (hT : 0 < T)
    (hlog : Real.log (2 * delta) = -T) :
    max (delta - t) 0 ≤ (delta / T) * |Real.log (t + delta)| := by
  by_cases htd : delta ≤ t
  · rw [max_eq_right (sub_nonpos.mpr htd)]
    exact mul_nonneg (div_nonneg hdelta.le hT.le) (abs_nonneg _)
  · have htd' : t < delta := lt_of_not_ge htd
    have hsmall : Real.log (t + delta) ≤ -T := by
      rw [← hlog]
      exact Real.log_le_log (by linarith) (by linarith)
    have hlarge : T ≤ |Real.log (t + delta)| := by
      linarith [neg_le_abs (Real.log (t + delta))]
    calc
      max (delta - t) 0 ≤ delta := max_le (sub_le_self _ ht) hdelta.le
      _ = (delta / T) * T := (div_mul_cancel₀ _ hT.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (div_nonneg hdelta.le hT.le)

/-- The preceding pointwise comparison gives the actual positive-part
norm bound, including for an almost-everywhere logarithmic representative. -/
private theorem raw_const_smul_finite {X : Type*} [MeasurableSpace X]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (c : ℝ) (f : X → ℝ) (mu : Measure X) :
    SubdiffusiveProcess.RawLp.eLpNorm (c • f) p mu = ‖c‖ₑ * SubdiffusiveProcess.RawLp.eLpNorm f p mu := by
  simpa only [SubdiffusiveProcess.RawLp.eLpNorm, ite_eq_right hp0, ite_eq_right hptop] using!
    (MeasureTheory.eLpNorm'_const_smul (μ := mu) (f := f) c
      (ENNReal.toReal_pos hp0 hptop))

theorem harmonic_positive_part_norm_le_log {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {h w : X → ℝ} {delta T : ℝ}
    (hh : ∀ᵐ x ∂mu, 0 ≤ h x) (hdelta : 0 < delta) (hT : 0 < T)
    (hlog : Real.log (2 * delta) = -T)
    (hw : ∀ᵐ x ∂mu, w x = Real.log (h x + delta)) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun x => max (delta - h x) 0) 2 mu ≤
      ENNReal.ofReal (delta / T) * SubdiffusiveProcess.RawLp.eLpNorm w 2 mu := by
  have hcoef : 0 ≤ delta / T := div_nonneg hdelta.le hT.le
  calc
    SubdiffusiveProcess.RawLp.eLpNorm (fun x => max (delta - h x) 0) 2 mu ≤ SubdiffusiveProcess.RawLp.eLpNorm ((delta / T) • w) 2 mu := by
      apply SubdiffusiveProcess.RawLp.eLpNorm_mono_ae
      filter_upwards [hh, hw] with x hx hwx
      simp only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg hcoef, abs_of_nonneg (le_max_right (delta - h x) 0)]
      rw [hwx]
      exact harmonic_positive_part_le_scaled_log hx hdelta hT hlog
    _ = _ := by
      rw [raw_const_smul_finite (p := 2) (by norm_num) (by norm_num), ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hcoef]

/-- Read a normalized square-integral bound as a normalized `L²` bound. -/
theorem harmonic_eLpNorm_two_le_sqrt_mass {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {w : X → ℝ} (hw : MemLp w 2 mu)
    (hM0 : mu Set.univ ≠ 0) (hMtop : mu Set.univ ≠ ⊤)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : (∫ x, w x ^ 2 ∂mu) ≤ C * (mu Set.univ).toReal) :
    eLpNorm w 2 mu ≤ ENNReal.ofReal (Real.sqrt C) * mu Set.univ ^ (1 / 2 : ℝ) := by
  have hreal : (eLpNorm w 2 mu).toReal ≤ Real.sqrt C * Real.sqrt (mu Set.univ).toReal := by
    calc
      (eLpNorm w 2 mu).toReal = Real.sqrt ((eLpNorm w 2 mu).toReal ^ 2) :=
        (Real.sqrt_sq ENNReal.toReal_nonneg).symm
      _ ≤ Real.sqrt (C * (mu Set.univ).toReal) := by
        rw [toReal_eLpNorm_two_sq_eq_integral_sq hw]
        exact Real.sqrt_le_sqrt hbound
      _ = _ := Real.sqrt_mul hC _
  apply (ENNReal.toReal_le_toReal hw.eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_ne_zero hM0 hMtop))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg C),
    ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  exact hreal

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
