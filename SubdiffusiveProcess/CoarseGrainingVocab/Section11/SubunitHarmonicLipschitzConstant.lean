import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzUnit
import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzArithmetic

/-! The explicit dimension-only constant and the scale cancellation in the final estimate. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
open MeasureTheory Homogenization Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
noncomputable section


def dimensionalCoefficientPrice (d : ℕ) : ℝ :=
  8 / smallContrastThreshold d (1/2:ℝ) * (1+Real.sqrt d)

def harmonicLipschitzPolynomialPrice (d : ℕ) : ℝ :=
  2 * unitLipschitzPrice d * boundedMultiplierCaccioppoliEndpointConst d *
    (1 + ((volume (smallContrastUnitBall d)).toReal)⁻¹) *
    dimensionalCoefficientPrice d ^ (d+1)

/-- An explicit dimension-only constant for the harmonic Lipschitz bound. -/
def harmonicLipschitzConstant (d : ℕ) : ℝ :=
  1 + harmonicLipschitzPolynomialPrice d + (d+1 : ℕ)

def interiorLipschitzPrice (d : ℕ) (H : ℝ) : ℝ :=
  2 * unitLipschitzPrice d * boundedMultiplierCaccioppoliEndpointConst d /
    interiorContrastFraction d H *
    Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
      interiorContrastFraction d H ^ d)⁻¹)


theorem dimensionalCoefficientPrice_nonneg (d : ℕ) : 0 ≤ dimensionalCoefficientPrice d := by
  have hthresh : 0 < smallContrastThreshold d (1/2:ℝ) :=
    Section9Support.WeightedLocalHarmonic.smallContrastThreshold_half_pos d
  have hsqrt : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hden : (0:ℝ) < 1 + Real.sqrt (d : ℝ) := by linarith
  have h1 : 0 ≤ 8 / smallContrastThreshold d (1/2:ℝ) := by
    apply div_nonneg _ (le_of_lt hthresh)
    norm_num
  have h2 : 0 ≤ (1 + Real.sqrt (d : ℝ)) := by linarith
  unfold dimensionalCoefficientPrice
  positivity

theorem harmonicLipschitzPolynomialPrice_nonneg (d : ℕ) :
  0 ≤ harmonicLipschitzPolynomialPrice d := by
  rw [harmonicLipschitzPolynomialPrice]
  have h1 := unitLipschitzPrice_nonneg d
  have h2 := boundedMultiplierCaccioppoliEndpointConst_nonneg d
  have h3 := dimensionalCoefficientPrice_nonneg d
  have h4 : 0 ≤ ((volume (smallContrastUnitBall d)).toReal)⁻¹ :=
    inv_nonneg.2 ENNReal.toReal_nonneg
  positivity

theorem harmonicLipschitzConstant_nonneg (d : ℕ) : 0 ≤ harmonicLipschitzConstant d := by
  unfold harmonicLipschitzConstant
  have h1 : 0 ≤ harmonicLipschitzPolynomialPrice d :=
    harmonicLipschitzPolynomialPrice_nonneg d
  have h2 : 0 ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.cast_nonneg (n := d + 1)
  positivity

theorem interiorLipschitzPrice_le {d : ℕ} [NeZero d] {H : ℝ} (hH : 1 ≤ H) :
    interiorLipschitzPrice d H ≤ harmonicLipschitzConstant d * Real.exp (harmonicLipschitzConstant d * H) := by
  have ha : 0 ≤ unitLipschitzPrice d := unitLipschitzPrice_nonneg d
  have hb : 0 ≤ boundedMultiplierCaccioppoliEndpointConst d :=
    boundedMultiplierCaccioppoliEndpointConst_nonneg d
  have hV : 0 < (volume (smallContrastUnitBall d)).toReal :=
    volume_smallContrastUnitBall_toReal_pos d
  have hf : 0 < interiorContrastFraction d H := interiorContrastFraction_pos d H
  have hf1 : interiorContrastFraction d H ≤ 1 :=
    le_trans (interiorContrastFraction_le d H) (by norm_num)
  have hA : 0 ≤ dimensionalCoefficientPrice d := dimensionalCoefficientPrice_nonneg d
  have hinv : (interiorContrastFraction d H)⁻¹ ≤ dimensionalCoefficientPrice d * H :=
    interiorContrastFraction_inv_le (d := d) hH
  have h1 := local_price_le_polynomial ha hb hV hf hf1 hA hH hinv d
  have h2 : interiorLipschitzPrice d H ≤ harmonicLipschitzPolynomialPrice d * H ^ (d + 1) := h1
  have hB : 0 ≤ harmonicLipschitzPolynomialPrice d := by
    unfold harmonicLipschitzPolynomialPrice
    have hVnn : 0 ≤ (volume (smallContrastUnitBall d)).toReal := le_of_lt hV
    have hip : 0 ≤ 1 + ((volume (smallContrastUnitBall d)).toReal)⁻¹ := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) hb) hip)
      (pow_nonneg hA _)
  have h3 := prefactor_polynomial_le hB hH (d + 1)
  exact le_trans h2 h3

theorem lipschitz_price_from_caccioppoli {ell f L A P E N S r : ℝ}
 (hell : 0 < ell) (hf : 0 < f) (hL : 0 ≤ L) (hA : 0 ≤ A) (hr : 0 ≤ r)
 (heq : P*(ell*f/2) = A*E) (hEN : E ≤ S*N) :
 L*P*r ≤ (2*L*A/f*S)*(r/ell)*N := by
  have hpos : 0 < ell*f/2 := by positivity
  have key : P*(ell*f/2) ≤ A*(S*N) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left hEN hA
  have hp : P ≤ (A*(S*N))/(ell*f/2) := (le_div_iff₀ hpos).2 key
  calc L*P*r ≤ L*((A*(S*N))/(ell*f/2))*r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hL) hr
    _ = (2*L*A/f*S)*(r/ell)*N := by field_simp [hell.ne', hf.ne']

theorem mem_euclideanBall_of_euclideanNorm_lt {d : ℕ} {x y : Vec d} {r : ℝ}
    (hr : 0 < r) (h : euclideanNorm (y-x) < r) : y ∈ euclideanBall x r := by
  have hs := (sq_lt_sq₀ (euclideanNorm_nonneg (y-x)) hr.le).2 h
  rw [euclideanNorm_sq] at hs
  exact hs
end
end SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
