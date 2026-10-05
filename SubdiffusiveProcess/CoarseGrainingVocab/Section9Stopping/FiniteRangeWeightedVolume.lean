module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- A pointwise exponential oscillation bound transfers to the corresponding two-sided
bound on extended nonnegative integrals. The caller may take `μ` to be the restriction of
volume to a ball or translated cube.

Source: `mfd:in-deterministic` and `s.tightness`.
-/
theorem lintegral_mul_exp_bounds (μ : Measure α) (base : α → ENNReal)
    (tail : α → ℝ) (ω : ℝ) (htail : ∀ x, |tail x| ≤ ω) :
    ENNReal.ofReal (Real.exp (-ω)) * ∫⁻ x, base x ∂μ ≤
        ∫⁻ x, base x * ENNReal.ofReal (Real.exp (tail x)) ∂μ ∧
      ∫⁻ x, base x * ENNReal.ofReal (Real.exp (tail x)) ∂μ ≤
        ENNReal.ofReal (Real.exp ω) * ∫⁻ x, base x ∂μ := by
  constructor
  · rw [← lintegral_const_mul' _ base ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    simpa only [mul_comm] using mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_of_abs_le (htail x))))
      (base x)
  · rw [← lintegral_const_mul' _ base ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    simpa only [mul_comm] using mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_abs_le (htail x))))
      (base x)

/-- Positive two-sided exponential comparison is equivalent to the logarithmic error bound
used in the weighted-volume estimate. Positivity is explicit, so no `log 0` or `toReal`
fallback is hidden.

Source: `mfd:in-deterministic` and `s.tightness`.
-/
theorem abs_log_div_le_of_exp_bounds {x y ω : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlower : Real.exp (-ω) * y ≤ x) (hupper : x ≤ Real.exp ω * y) :
    |Real.log (x / y)| ≤ ω := by
  rw [abs_le]
  constructor
  · rw [Real.le_log_iff_exp_le (div_pos hx hy)]
    exact (le_div_iff₀ hy).2 hlower
  · rw [Real.log_le_iff_le_exp (div_pos hx hy)]
    exact (div_le_iff₀ hy).2 hupper

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
