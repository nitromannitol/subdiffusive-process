import SubdiffusiveProcess.Section10.SmallDisplacement
import SubdiffusiveProcess.Probability.ExponentialTailMoment



open Filter MeasureTheory ProbabilityTheory MarkovProcess Set Topology SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.SmallDisplacement

/-- Coefficient from the existing exponential-tail integrator. -/
def negativeMomentConstant (C A q : ℝ) : ℝ :=
  1 + C * Real.exp q / (1 - Real.exp (q - A))

lemma negativeMomentConstant_pos (C A q : ℝ) (hC : 0 ≤ C) (hgap : q < A) :
    0 < negativeMomentConstant C A q := by
  have hden : 0 < 1 - Real.exp (q - A) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr hgap))
  unfold negativeMomentConstant
  exact add_pos_of_pos_of_nonneg (by norm_num)
    (div_nonneg (mul_nonneg hC (Real.exp_pos _).le) hden.le)

/-- A positive small-ball exponent excludes a zero value almost surely. -/
lemma zero_null_of_small_ball {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (C A : ℝ) (hA : 0 < A)
    (hsmall : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      P {w | Y w ≤ epsilon} ≤ ENNReal.ofReal (C * epsilon ^ A)) :
    P {w | Y w = 0} = 0 := by
  have hexp : ∀ n : ℕ, P {w | Y w = 0} ≤ ENNReal.ofReal (C * Real.exp (-A * (n : ℝ))) := by
    intro n
    have h := hsmall (Real.exp (-(n : ℝ))) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n)))
    have heq : Real.exp (-(n : ℝ)) ^ A = Real.exp (-A * (n : ℝ)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [heq] at h
    exact (measure_mono (fun w (hw : Y w = 0) => by change Y w ≤ Real.exp (-(n : ℝ)); rw [hw]; exact (Real.exp_pos _).le)).trans h
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * Real.exp (-A * (n : ℝ)))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 A hA).comp
      tendsto_natCast_atTop_atTop).const_mul C
    simpa only [Function.comp_def, Real.rpow_zero, one_mul, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hexp) (zero_le _)

/-- Consume the canonical exponential-tail-to-moment theorem after logarithmic
ceiling discretization. No new classical integration theorem is developed. -/
theorem negative_moment_of_small_ball {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (hY0 : ∀ w, 0 ≤ Y w) (C A q : ℝ) (hC : 0 ≤ C) (hA : 0 < A)
    (hq : 0 < q) (hqA : q < A)
    (hsmall : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      P {w | Y w ≤ epsilon} ≤ ENNReal.ofReal (C * epsilon ^ A)) :
    (∫⁻ w, ENNReal.ofReal (Y w) ^ (-q) ∂P) ≤ ENNReal.ofReal (negativeMomentConstant C A q) := by
  let B : Ω → ℕ := fun w => Nat.ceil (max (-Real.log (Y w)) 0)
  have hB : Measurable B := (hY.log.neg.max measurable_const).nat_ceil
  have htail : ∀ n : ℕ, P.real {w | n < B w} ≤ C * Real.exp (-A * (n : ℝ)) := by
    intro n
    have hinc : {w | n < B w} ⊆ {w | Y w ≤ Real.exp (-(n : ℝ))} := by
      intro w hw
      change Y w ≤ Real.exp (-(n : ℝ))
      have hmax : (n : ℝ) < max (-Real.log (Y w)) 0 := Nat.lt_ceil.mp hw
      have hlog : (n : ℝ) < -Real.log (Y w) := by
        rcases lt_max_iff.mp hmax with h | h
        · exact h
        · exact False.elim ((not_lt_of_ge (Nat.cast_nonneg n)) h)
      rcases eq_or_lt_of_le (hY0 w) with hzero | hpos
      · rw [← hzero]
        exact (Real.exp_pos _).le
      · exact ((Real.log_lt_iff_lt_exp hpos).mp (by linarith)).le
    have hb := hsmall (Real.exp (-(n : ℝ))) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n)))
    have heq : Real.exp (-(n : ℝ)) ^ A = Real.exp (-A * (n : ℝ)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [heq] at hb
    calc P.real {w | n < B w} ≤ P.real {w | Y w ≤ Real.exp (-(n : ℝ))} := measureReal_mono hinc
      _ ≤ (ENNReal.ofReal (C * Real.exp (-A * (n : ℝ)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = _ := ENNReal.toReal_ofReal (mul_nonneg hC (Real.exp_pos _).le)
  obtain ⟨hint, hbound⟩ := integrable_exp_nat_of_exponential_tail P B hB C A q hC hq.le hqA htail
  have hpositive : ∀ᵐ w ∂P, 0 < Y w := by
    have hz := zero_null_of_small_ball P Y C A hA hsmall
    have hne : ∀ᵐ w ∂P, Y w ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using hz
    filter_upwards [hne] with w hw
    exact lt_of_le_of_ne (hY0 w) hw.symm
  have hpoint : ∀ᵐ w ∂P, ENNReal.ofReal (Y w) ^ (-q) ≤
      ENNReal.ofReal (Real.exp (q * (B w : ℝ))) := by
    filter_upwards [hpositive] with w hw
    rw [ENNReal.ofReal_rpow_of_pos hw]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_def_of_pos hw]
    apply Real.exp_le_exp.mpr
    have hceil : -Real.log (Y w) ≤ (B w : ℝ) :=
      (le_max_left _ _).trans (Nat.le_ceil _)
    nlinarith only [mul_le_mul_of_nonneg_left hceil hq.le]
  calc (∫⁻ w, ENNReal.ofReal (Y w) ^ (-q) ∂P)
      ≤ ∫⁻ w, ENNReal.ofReal (Real.exp (q * (B w : ℝ))) ∂P := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (∫ w, Real.exp (q * (B w : ℝ)) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ => (Real.exp_pos _).le))).symm
    _ ≤ ENNReal.ofReal (negativeMomentConstant C A q) := ENNReal.ofReal_le_ofReal hbound

end SubdiffusiveProcess.Section10.SmallDisplacement
