import SubdiffusiveProcess.CoarseGrainingVocab.Section10Nash.TwoDimGeneralExponent

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section10Nash
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- The Sobolev exponent corresponding to effective dimension 2d. -/
def sobolevExponent (d : ℕ) (hd : 2 ≤ d) : FiniteLpExponent where
  exponent := ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))
  one_lt := by
    rw [ENNReal.one_lt_ofReal, lt_div_iff₀]
    · have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    · have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
  lt_top := ENNReal.ofReal_lt_top

theorem sobolevExponent_two_lt (d : ℕ) (hd : 2 ≤ d) :
    (2 : ℝ≥0∞) < (sobolevExponent d hd).exponent := by
  change 2 < ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))
  rw [ENNReal.ofNat_lt_ofReal, lt_div_iff₀]
  · have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  · have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith

theorem sobolevExponent_theta (d : ℕ) (hd : 2 ≤ d) :
    twoDimNashThetaOfExponent (sobolevExponent d hd) = 1 / (d : ℝ) := by
  have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  unfold twoDimNashThetaOfExponent sobolevExponent
  rw [ENNReal.toReal_ofReal (div_nonneg (by positivity) (by linarith))]
  field_simp [hd0, hd1]
  ring

/-- The interpolation inequality with the exponent used in the frozen Nash command. -/
theorem nash_interpolation {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (d : ℕ) (hd : 2 ≤ d) (f : X → ℝ) (hf : AEStronglyMeasurable f mu) :
    eLpNorm f 2 mu ^ (2 * (1 + 1 / (d : ℝ)) : ℝ) ≤
      eLpNorm f 1 mu ^ (2 / (d : ℝ) : ℝ) *
        eLpNorm f (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))) mu ^ (2 : ℕ) := by
  have h := eLpNorm_two_dim_nash_interpolation mu f (sobolevExponent d hd)
    (sobolevExponent_two_lt d hd) hf
  dsimp only at h
  rw [sobolevExponent_theta] at h
  simpa only [sobolevExponent, mul_one_div, ENNReal.rpow_two] using h

/-- Substitution of the generator-domain Sobolev estimate into Nash interpolation. -/
theorem nash_of_sobolev {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (d : ℕ) (hd : 2 ≤ d) (f : X → ℝ) (hf : AEStronglyMeasurable f mu) (K E : ℝ≥0∞)
    (hsob : eLpNorm f (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))) mu ^ (2 : ℕ) ≤ K * E) :
    eLpNorm f 2 mu ^ (2 * (1 + 1 / (d : ℝ)) : ℝ) ≤
      K * E * eLpNorm f 1 mu ^ (2 / (d : ℝ) : ℝ) := by
  exact (nash_interpolation mu d hd f hf).trans
    ((mul_le_mul_right hsob _).trans_eq (mul_comm _ _))

end SubdiffusiveProcess.Nash
