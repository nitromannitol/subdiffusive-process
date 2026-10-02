import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzIteration

/-! Explicit polynomial and exponential bounds for the localization constants. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
open MeasureTheory Homogenization Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
noncomputable section

open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
theorem one_le_of_logCoefficientControlOn {d : ℕ} {a : Vec d → ℝ} {H : ℝ} {U : SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.Cube d}
 (hc : LogCoefficientControlOn a H U) : 1 ≤ H := by
  rcases hc with ⟨hpos, G, K, hG, hK, hdiff, hgrad, hholder, hscale⟩
  nlinarith [mul_nonneg (sq_nonneg U.2) (sq_nonneg G), mul_nonneg (sq_nonneg U.2) hK]

theorem log_lipschitz_radius_guard {d : ℕ} {H ell : ℝ} (hell : 0 < ell) :
 Real.sqrt d * (Real.sqrt H / ell) * (ell * interiorContrastFraction d H) ≤
 smallContrastThreshold d (1/2:ℝ) / 8 := by
  have hS : 0 ≤ Real.sqrt d * Real.sqrt H :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h1S : (0:ℝ) < 1 + Real.sqrt d * Real.sqrt H := by linarith
  have h8 : (0:ℝ) < 8 := by norm_num
  unfold interiorContrastFraction smallContrastThreshold
  field_simp [hell.ne', h1S]
  norm_num

theorem polynomial_le_exponential {H : ℝ} (hH : 0 ≤ H) (n : ℕ) :
 H ^ n ≤ Real.exp ((n:ℝ) * H) := by
  have hle : H ≤ Real.exp H := by linarith [Real.add_one_le_exp H]
  have h1 : 0 ≤ Real.exp H := Real.exp_nonneg _
  have h2 : H ^ n ≤ (Real.exp H) ^ n := pow_le_pow_left₀ hH hle n
  have h3 : (Real.exp H) ^ n = Real.exp ((n:ℝ) * H) := by
    rw [← Real.exp_nat_mul]
  rw [h3] at h2
  exact h2

theorem prefactor_polynomial_le {B H : ℝ} (hB : 0 ≤ B) (hH : 1 ≤ H) (n : ℕ) :
    B * H ^ n ≤ (1+B+n) * Real.exp ((1+B+n) * H) := by
  have hH0 : 0 ≤ H := by linarith
  have hC : 0 ≤ 1+B+(n:ℝ) := by positivity
  have hBbound : B ≤ 1+B+(n:ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have he : Real.exp ((n:ℝ)*H) ≤ Real.exp ((1+B+(n:ℝ))*H) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (show (n:ℝ) ≤ 1+B+(n:ℝ) by linarith) hH0)
  calc B * H ^ n ≤ B * Real.exp ((n:ℝ)*H) :=
      mul_le_mul_of_nonneg_left (polynomial_le_exponential hH0 n) hB
    _ ≤ (1+B+(n:ℝ)) * Real.exp ((1+B+(n:ℝ))*H) :=
      mul_le_mul hBbound he (Real.exp_pos _).le hC

theorem sqrt_mul_le_linear {x t : ℝ} (hx : 0 ≤ x) (ht : 1 ≤ t) :
 Real.sqrt (x*t) ≤ (1+x)*t := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hQ : 0 ≤ (1+x)*t := mul_nonneg (by linarith) ht0
  have hkey : x*t ≤ ((1+x)*t)^2 := by
    nlinarith [sq_nonneg (1 + x - Real.sqrt x), sq_nonneg (t - 1),
      mul_nonneg hx ht0]
  exact (Real.sqrt_le_iff.mpr ⟨hQ, hkey⟩)

theorem volume_sqrt_price {V f : ℝ} (hV : 0 < V) (hf : 0 < f) (hf1 : f ≤ 1) (d : ℕ) :
 Real.sqrt ((V*f^d)⁻¹) ≤ (1+V⁻¹)*(f⁻¹)^d := by
  have hft : 1 ≤ (f⁻¹ : ℝ) := ((one_le_inv₀ hf).2 hf1)
  have ht : 1 ≤ (f⁻¹ : ℝ)^d := one_le_pow₀ hft
  have hx : 0 ≤ (V⁻¹ : ℝ) := le_of_lt (inv_pos.2 hV)
  simpa only [mul_inv, inv_pow] using (sqrt_mul_le_linear hx ht)

theorem interiorContrastFraction_inv_le {d : ℕ} {H : ℝ} (hH : 1 ≤ H) :
 (interiorContrastFraction d H)⁻¹ ≤
 (8 / smallContrastThreshold d (1/2:ℝ) * (1+Real.sqrt d)) * H := by
  have hδ : 0 < smallContrastThreshold d (1/2:ℝ) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.smallContrastThreshold_half_pos d
  have hH0 : 0 ≤ H := by linarith
  have hsqH : Real.sqrt H ≤ H :=
    Real.sqrt_le_iff.mpr ⟨hH0, by nlinarith⟩
  have hkey : 1 + Real.sqrt d * Real.sqrt H ≤ (1 + Real.sqrt d) * H := by
    have hd : Real.sqrt d * Real.sqrt H ≤ Real.sqrt d * H :=
      mul_le_mul_of_nonneg_left hsqH (Real.sqrt_nonneg d)
    nlinarith [hd, Real.sqrt_nonneg d, hH]
  have hpos : 0 ≤ 8 / smallContrastThreshold d (1/2:ℝ) :=
    div_nonneg (by norm_num) (le_of_lt hδ)
  have heq : (interiorContrastFraction d H)⁻¹
      = (8 / smallContrastThreshold d (1/2:ℝ)) * (1+Real.sqrt d*Real.sqrt H) := by
    unfold interiorContrastFraction
    rw [inv_div]
    ring
  rw [heq]
  simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hkey hpos)

theorem local_price_le_polynomial {a b V f A H : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
 (hV : 0 < V) (hf : 0 < f) (hf1 : f ≤ 1) (_hA : 0 ≤ A) (_hH : 1 ≤ H)
 (hinv : f⁻¹ ≤ A*H) (d : ℕ) :
 2*a*b/f * Real.sqrt ((V*f^d)⁻¹) ≤
 (2*a*b*(1+V⁻¹)*A^(d+1))*H^(d+1) := by
  have hcoef : 0 ≤ 2*a*b*(1+V⁻¹) := by positivity
  have hsqrt := volume_sqrt_price hV hf hf1 d
  have hstep : (2*a*b/f)*((1+V⁻¹)*(f⁻¹)^d) = 2*a*b*(1+V⁻¹)*(f⁻¹)^(d+1) := by
    rw [div_eq_mul_inv, pow_succ]; ring
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hf.le) hinv (d+1)
  calc 2*a*b/f * Real.sqrt ((V*f^d)⁻¹)
      ≤ (2*a*b/f)*((1+V⁻¹)*(f⁻¹)^d) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 2*a*b*(1+V⁻¹)*(f⁻¹)^(d+1) := hstep
    _ ≤ 2*a*b*(1+V⁻¹)*(A*H)^(d+1) :=
        mul_le_mul_of_nonneg_left hpow hcoef
    _ = (2*a*b*(1+V⁻¹)*A^(d+1))*H^(d+1) := by
        rw [mul_pow]; ring
end
end SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
