module

public import SubdiffusiveProcess.Section10.ExitLowerMoments

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The source's random early-exit envelope gives its lower mean-exit bound
at time (2K)^(-2), with the original physical clock. -/
theorem meanExit_ge_of_fast_exit {W : Type*} [MeasurableSpace W]
    (P : Measure W) [IsProbabilityMeasure P] (tau : W → ℝ≥0∞) (htau : Measurable tau)
    {K clock : ℝ} (hK : 1 ≤ K) (hclock : 0 < clock)
    (hfast : ∀ t : ℝ, 0 < t →
      P {w | tau w ≤ ENNReal.ofReal (t * clock)} ≤ ENNReal.ofReal (K * Real.sqrt t)) :
    ENNReal.ofReal ((1 / 8 : ℝ) * K ^ (-2 : ℤ) * clock) ≤ ∫⁻ w, tau w ∂P := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let t : ℝ := ((2 * K)⁻¹) ^ 2
  have ht : 0 < t := sq_pos_of_pos (inv_pos.mpr (mul_pos (by norm_num) hKpos))
  have hsqrt : K * Real.sqrt t = 1 / 2 := by
    rw [Real.sqrt_sq (inv_nonneg.mpr (mul_nonneg (by norm_num) hKpos.le))]
    field_simp
  let c := Real.toNNReal (t * clock)
  have hf : P {w | tau w ≤ (c : ℝ≥0∞)} ≤ (1 / 2 : ℝ≥0∞) := by
    have h := hfast t ht
    rw [hsqrt] at h
    exact h.trans_eq (by norm_num [ENNReal.ofReal_div_of_pos])
  have hs : (1 / 2 : ℝ≥0∞) ≤ P {w | (c : ℝ≥0∞) < tau w} := by
    have h := ExitLowerMoments.survival_lower_of_fast_exit P tau htau c (1 / 2) hf
    norm_num at h ⊢
    exact h
  have hm := ExitLowerMoments.survival_mul_rpow_le_moment P tau htau c 1 (by norm_num)
  simp only [ENNReal.rpow_one] at hm
  have hfactor : (1 / 8 : ℝ) * K ^ (-2 : ℤ) * clock = (t * clock) * (1 / 2) := by
    dsimp only [t]
    rw [zpow_neg, zpow_ofNat]
    field_simp
    ring
  calc
    _ = (c : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) := by
      rw [hfactor, ENNReal.ofReal_mul (mul_nonneg ht.le hclock.le)]
      change ENNReal.ofReal (t * clock) * ENNReal.ofReal (1 / 2) =
        ENNReal.ofReal (t * clock) * (1 / 2)
      congr 1
      norm_num [ENNReal.ofReal_div_of_pos]
    _ ≤ (c : ℝ≥0∞) * P {w | (c : ℝ≥0∞) < tau w} := mul_le_mul_right hs _
    _ ≤ _ := hm

end SubdiffusiveProcess.Section10
