import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ScaleZeroPointEndpoint
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitRadiusAbsorption
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.ScaleZeroPointReadout

/-!
# Theta ladder: scale-zero price absorption

The positive-parent scale-zero endpoint loses a power of `sqrt m + 1`.
This is absorbed into one eighth of the parent-scale exponent, uniformly in
the parent scale.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

private theorem sqrt_inv_mul_three_negQuarter
    {A : ℝ} (hA : 0 < A) (m : ℕ) :
    Real.sqrt ((A * (3 : ℝ) ^ (-(m : ℝ) / 4))⁻¹) =
      Real.sqrt A⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 8) := by
  have hp : 0 < (3 : ℝ) ^ (-(m : ℝ) / 4) := by positivity
  rw [mul_inv, Real.sqrt_mul (inv_nonneg.mpr hA.le)]
  congr 1
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- The literal positive-scale price is bounded by a dimension-only constant
times `3^(m/8)`. -/
theorem exists_positiveScaleZeroPointPrice_exponential_bound
    (d : ℕ) [NeZero d] :
    ∃ Kpoint : ℝ, 0 < Kpoint ∧
      ∀ m : ℕ, 0 < m →
        positiveScaleZeroPointPrice d m ≤
          Kpoint * (3 : ℝ) ^ ((m : ℝ) / 8) := by
  have hdNat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let rate : ℝ := 1 / (4 * (d : ℝ))
  have hrate : 0 < rate := by dsimp only [rate]; positivity
  have hrateLog : rate * Real.log 3 ≤ 1 := by
    have hlogLe0 : Real.log (3 : ℝ) ≤ 3 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have hlogLe : Real.log 3 ≤ 3 := by linarith
    dsimp only [rate]
    rw [div_mul_eq_mul_div]
    have hdOne : 1 ≤ (d : ℝ) := by exact_mod_cast hdNat
    apply (div_le_iff₀ (by positivity : 0 < 4 * (d : ℝ))).2
    nlinarith
  let A : ℝ := (rate * Real.log 3)⁻¹
  have hA : 0 < A := inv_pos.mpr (mul_pos hrate hlog)
  let Rbase : ℝ := boundedMultiplierRadiusFloor d / A
  have hRbase : 0 < Rbase := div_pos (boundedMultiplierRadiusFloor_pos d) hA
  let Kpoint := boundedMultiplierScaleZeroL2Price d Rbase
  have hV : 0 < (volume (smallContrastUnitBall d)).toReal := by
    unfold smallContrastUnitBall
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero
        (0 : Vec d) (by norm_num : (0 : ℝ) < 1)))
  have hKpoint : 0 < Kpoint := by
    dsimp only [Kpoint, boundedMultiplierScaleZeroL2Price]
    have hden : 0 < (volume (smallContrastUnitBall d)).toReal *
        (Rbase / 4) ^ d := mul_pos hV (pow_pos (by positivity) d)
    have hroot : 0 < Real.sqrt
        (((volume (smallContrastUnitBall d)).toReal * (Rbase / 4) ^ d)⁻¹) :=
      Real.sqrt_pos.2 (inv_pos.mpr hden)
    have hfirst : 0 ≤ smallContrastSchauderConstant d *
        boundedMultiplierCaccioppoliEndpointConst d *
        Real.sqrt (((volume (smallContrastUnitBall d)).toReal * Rbase ^ d)⁻¹) :=
      mul_nonneg
        (mul_nonneg (smallContrastSchauderConstant_nonneg d)
          (boundedMultiplierCaccioppoliEndpointConst_nonneg d))
        (Real.sqrt_nonneg _)
    linarith
  refine ⟨Kpoint, hKpoint, ?_⟩
  intro m hm
  have hmOne : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hsqrt := sqrt_add_one_le_inv_mul_three_rpow hmOne hrate hrateLog
  have hsqrtA : Real.sqrt (m : ℝ) + 1 ≤
      A * (3 : ℝ) ^ (rate * (m : ℝ)) := by
    simpa only [A] using hsqrt
  let R0 := Rbase * (3 : ℝ) ^ (-(rate * (m : ℝ)))
  have hR0 : 0 < R0 := mul_pos hRbase (by positivity)
  have hden : 0 < Real.sqrt (m : ℝ) + 1 := by
    linarith [Real.sqrt_nonneg (m : ℝ)]
  have hR0le : R0 ≤ boundedMultiplierRadiusFloor d /
      (Real.sqrt (m : ℝ) + 1) := by
    rw [le_div_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_left hsqrtA hR0.le
    have hcancel : R0 * (A * (3 : ℝ) ^ (rate * (m : ℝ))) =
        boundedMultiplierRadiusFloor d := by
      dsimp only [R0, Rbase]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      field_simp [hA.ne', (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne']
    rw [hcancel] at hmul
    exact hmul
  have hmono := boundedMultiplierScaleZeroL2Price_antitone (d := d)
    hR0 (div_pos (boundedMultiplierRadiusFloor_pos d) hden) hR0le
  have hrateD : rate * (d : ℝ) = 1 / 4 := by
    dsimp only [rate]
    field_simp [hd.ne']
  have hpowR0 : R0 ^ d = Rbase ^ d *
      (3 : ℝ) ^ (-(m : ℝ) / 4) := by
    dsimp only [R0]
    rw [mul_pow]
    have hp : ((3 : ℝ) ^ (-(rate * (m : ℝ)))) ^ d =
        (3 : ℝ) ^ (-(rate * (m : ℝ)) * (d : ℝ)) := by
      calc
        ((3 : ℝ) ^ (-(rate * (m : ℝ)))) ^ d =
            ((3 : ℝ) ^ (-(rate * (m : ℝ)))) ^ (d : ℝ) := by
          rw [Real.rpow_natCast]
        _ = (3 : ℝ) ^ (-(rate * (m : ℝ)) * (d : ℝ)) :=
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
    rw [hp]
    rw [show -(rate * (m : ℝ)) * (d : ℝ) = -(m : ℝ) / 4 by
      nlinarith [hrateD]]
  have hpowQuarter : (R0 / 4) ^ d = (Rbase / 4) ^ d *
      (3 : ℝ) ^ (-(m : ℝ) / 4) := by
    calc
      (R0 / 4) ^ d = R0 ^ d / (4 : ℝ) ^ d := div_pow R0 4 d
      _ = (Rbase ^ d * (3 : ℝ) ^ (-(m : ℝ) / 4)) /
          (4 : ℝ) ^ d := by rw [hpowR0]
      _ = (Rbase ^ d / (4 : ℝ) ^ d) *
          (3 : ℝ) ^ (-(m : ℝ) / 4) := by ring
      _ = (Rbase / 4) ^ d *
          (3 : ℝ) ^ (-(m : ℝ) / 4) :=
        congrArg (fun t : ℝ ↦ t * (3 : ℝ) ^ (-(m : ℝ) / 4))
          (div_pow Rbase 4 d).symm
  have houter : Real.sqrt
      (((volume (smallContrastUnitBall d)).toReal * R0 ^ d)⁻¹) =
      Real.sqrt (((volume (smallContrastUnitBall d)).toReal * Rbase ^ d)⁻¹) *
        (3 : ℝ) ^ ((m : ℝ) / 8) := by
    rw [hpowR0, ← mul_assoc]
    exact sqrt_inv_mul_three_negQuarter
      (mul_pos hV (pow_pos hRbase d)) m
  have hinner : Real.sqrt
      (((volume (smallContrastUnitBall d)).toReal * (R0 / 4) ^ d)⁻¹) =
      Real.sqrt
          (((volume (smallContrastUnitBall d)).toReal * (Rbase / 4) ^ d)⁻¹) *
        (3 : ℝ) ^ ((m : ℝ) / 8) := by
    rw [hpowQuarter, ← mul_assoc]
    exact sqrt_inv_mul_three_negQuarter
      (mul_pos hV (pow_pos (by positivity : 0 < Rbase / 4) d)) m
  refine hmono.trans ?_
  dsimp only [positiveScaleZeroPointPrice]
  change boundedMultiplierScaleZeroL2Price d R0 ≤ _
  rw [boundedMultiplierScaleZeroL2Price, houter, hinner]
  dsimp only [Kpoint, boundedMultiplierScaleZeroL2Price]
  ring_nf
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
