import SubdiffusiveProcess.Section10.ExitLowerMoments
import SubdiffusiveProcess.Section10.ExitLowerMomentsPaleyZygmund

/-! A thin application of the pinned Paley--Zygmund theorem, for passage from
the physical random mean bank to every positive moment, including p below one.
The semigroup second-moment supplier is the completed ExitTailMoments module. -/
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.ExitLowerMoments

/-- A lower mean and a finite upper second moment give survival above half the
guaranteed mean. This consumes the existing scalar Paley--Zygmund theorem. -/
theorem survival_lower_of_mean_and_second_moment {W : Type*} [MeasurableSpace W]
    (mu : Measure W) [IsProbabilityMeasure mu] (tau : W → ℝ≥0∞)
    (htau : Measurable tau) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hlow : ENNReal.ofReal A ≤ ∫⁻ w, tau w ∂mu)
    (hsecond : (∫⁻ w, tau w ^ (2 : ℕ) ∂mu) ≤ ENNReal.ofReal B) :
    ENNReal.ofReal (A^2/(4*B)) ≤ mu {w | ENNReal.ofReal (A/2) ≤ tau w} := by
  have hfin : (∫⁻ w, tau w ∂mu) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (lintegral_le_rpow_lintegral_sq mu htau.aemeasurable)
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsecond)
  have hpz := lintegral_sq_mul_measure_ge_le mu htau hfin (1/2 : ℝ≥0)
  have hhalf : (((1/2 : ℝ≥0) : ℝ≥0∞)) = (1/2 : ℝ≥0∞) := by norm_num
  rw [hhalf] at hpz
  have hsub : mu {w | (1/2 : ℝ≥0∞)*(∫⁻ v, tau v ∂mu) ≤ tau w} ≤
      mu {w | ENNReal.ofReal (A/2) ≤ tau w} := by
    apply measure_mono
    intro w hw
    change (1/2 : ℝ≥0∞)*(∫⁻ v, tau v ∂mu) ≤ tau w at hw
    change ENNReal.ofReal (A/2) ≤ tau w
    apply le_trans _ hw
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm]
    simpa only [one_div] using mul_le_mul_right hlow (1/2 : ℝ≥0∞)
  have hnum : ENNReal.ofReal (A^2/4) ≤
      ENNReal.ofReal B * mu {w | ENNReal.ofReal (A/2) ≤ tau w} := by
    calc
      _ = ((1 : ℝ≥0∞)-1/2)^2 * ENNReal.ofReal A^2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
          ENNReal.ofReal_pow hA.le, ENNReal.ofReal_ofNat]
        norm_num
        rw [div_eq_mul_inv, ← ENNReal.inv_pow]
        norm_num [mul_comm]
      _ ≤ ((1 : ℝ≥0∞)-1/2)^2 * (∫⁻ w, tau w ∂mu)^2 := by gcongr
      _ ≤ _ := hpz.trans (mul_le_mul' hsecond hsub)
  have hdiv := ENNReal.div_le_of_le_mul (hnum.trans_eq (mul_comm _ _))
  convert hdiv using 1
  rw [← ENNReal.ofReal_div_of_pos hB]
  congr 1
  ring

/-- An event lower bound gives all real positive moments. In particular the
argument does not apply Jensen to the first moment when p is below one. -/
theorem moment_lower_of_mean_and_second_moment {W : Type*} [MeasurableSpace W]
    (mu : Measure W) [IsProbabilityMeasure mu] (tau : W → ℝ≥0∞)
    (htau : Measurable tau) (A B p : ℝ) (hA : 0 < A) (hB : 0 < B) (hp : 0 < p)
    (hlow : ENNReal.ofReal A ≤ ∫⁻ w, tau w ∂mu)
    (hsecond : (∫⁻ w, tau w ^ (2 : ℕ) ∂mu) ≤ ENNReal.ofReal B) :
    ENNReal.ofReal ((A/4)^p * (A^2/(4*B))) ≤ ∫⁻ w, tau w ^ p ∂mu := by
  have hs := survival_lower_of_mean_and_second_moment mu tau htau A B hA hB hlow hsecond
  have hsurv : ENNReal.ofReal (A^2/(4*B)) ≤
      mu {w | (Real.toNNReal (A/4) : ℝ≥0∞) < tau w} := by
    apply hs.trans
    apply measure_mono
    intro w hw
    change ENNReal.ofReal (A/2) ≤ tau w at hw
    change ENNReal.ofReal (A/4) < tau w
    exact lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)) hw
  have hm := survival_mul_rpow_le_moment mu tau htau (Real.toNNReal (A/4)) p hp
  calc
    _ = (Real.toNNReal (A/4) : ℝ≥0∞)^p * ENNReal.ofReal (A^2/(4*B)) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) p),
        ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le]
      rfl
    _ ≤ _ := (mul_le_mul_right hsurv _).trans hm

end SubdiffusiveProcess.Section10.ExitLowerMoments
