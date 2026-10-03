module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeWeightedVolume

@[expose] public section

/-!
# Finite real readout of the weighted-volume comparison

The Section 9 weighted-volume estimate is stated with a real logarithm, while weighted
integrals naturally take values in `ENNReal`. This file proves that the deterministic
comparison supplies the positivity and finiteness needed for the real readout.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]



theorem lintegral_mul_exp_ne_zero_and_ne_top (μ : Measure α)
    (base : α → ENNReal) (tail : α → ℝ) (ω : ℝ)
    (htail : ∀ x, |tail x| ≤ ω)
    (hbaseZero : (∫⁻ x, base x ∂μ) ≠ 0)
    (hbaseTop : (∫⁻ x, base x ∂μ) ≠ ⊤) :
    (∫⁻ x, base x * ENNReal.ofReal (Real.exp (tail x)) ∂μ) ≠ 0 ∧
      (∫⁻ x, base x * ENNReal.ofReal (Real.exp (tail x)) ∂μ) ≠ ⊤ := by
  have hbounds := lintegral_mul_exp_bounds μ base tail ω htail
  constructor
  · apply ne_of_gt
    apply lt_of_lt_of_le _ hbounds.1
    exact ENNReal.mul_pos
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos (-ω))) hbaseZero
  · exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbaseTop) hbounds.2



theorem toReal_lintegral_mul_exp_bounds (μ : Measure α)
    (base : α → ENNReal) (tail : α → ℝ) (ω : ℝ)
    (htail : ∀ x, |tail x| ≤ ω)
    (hbaseTop : (∫⁻ x, base x ∂μ) ≠ ⊤) :
    Real.exp (-ω) * (∫⁻ x, base x ∂μ).toReal ≤
        (∫⁻ x, base x * ENNReal.ofReal (Real.exp (tail x)) ∂μ).toReal ∧
      (∫⁻ x, base x * ENNReal.ofReal (Real.exp (tail x)) ∂μ).toReal ≤
        Real.exp ω * (∫⁻ x, base x ∂μ).toReal := by
  have hbounds := lintegral_mul_exp_bounds μ base tail ω htail
  have hweightedTop :
      (∫⁻ x, base x * ENNReal.ofReal (Real.exp (tail x)) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbaseTop) hbounds.2
  constructor
  · have hreal := ENNReal.toReal_mono hweightedTop hbounds.1
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos (-ω)).le] using hreal
  · have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbaseTop) hbounds.2
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos ω).le] using hreal



theorem abs_log_toReal_lintegral_ratio_le (μ : Measure α)
    (base : α → ENNReal) (tail : α → ℝ) (ω : ℝ)
    (htail : ∀ x, |tail x| ≤ ω)
    (hbaseZero : (∫⁻ x, base x ∂μ) ≠ 0)
    (hbaseTop : (∫⁻ x, base x ∂μ) ≠ ⊤) :
    |Real.log
      ((∫⁻ x, base x * ENNReal.ofReal (Real.exp (tail x)) ∂μ).toReal /
        (∫⁻ x, base x ∂μ).toReal)| ≤ ω := by
  have hweighted :=
    lintegral_mul_exp_ne_zero_and_ne_top μ base tail ω htail hbaseZero hbaseTop
  have hbounds := toReal_lintegral_mul_exp_bounds μ base tail ω htail hbaseTop
  exact abs_log_div_le_of_exp_bounds
    (ENNReal.toReal_pos hweighted.1 hweighted.2)
    (ENNReal.toReal_pos hbaseZero hbaseTop) hbounds.1 hbounds.2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
