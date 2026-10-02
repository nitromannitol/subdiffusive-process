import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy

theorem weightedEnergy_step_exponent {D p : ℝ} (h : -(1 / 2 : ℝ) + D * (1 / 2 - 1 / p) + 3 / (8 * p) ≤ -(1 / 4 : ℝ)) (j : ℕ) : (3 / 8 : ℝ) * ((j : ℝ) + 1) / p + (D * ((j : ℝ) + 1)) * (1 / 2 - 1 / p) - (j : ℝ) / 2 ≤ (1 / 4 : ℝ) - (j : ℝ) / 4 := by
  have h1 := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ)≤(j:ℝ)+1)
  ring_nf at h1 ⊢
  linarith

theorem weightedEnergy_ofReal_three_rpow (a : ℝ) : ENNReal.ofReal ((3 : ℝ) ^ a) = (3 : ℝ≥0∞) ^ a := by
  simpa using (ENNReal.ofReal_rpow_of_pos (x := 3) (p := a) (by norm_num)).symm

theorem weightedEnergy_ofReal_K_rpow (K p : ℝ) (hK : 0 ≤ K) (hp : 0 < p) : (ENNReal.ofReal K) ^ (1 / p) = ENNReal.ofReal (K ^ (1 / p)) := by
  exact ENNReal.ofReal_rpow_of_nonneg hK (by positivity)

theorem weightedEnergy_density_factor (S : ℝ) (hS : 0 ≤ S) (j : ℕ) : ENNReal.ofReal (2 * S * (3 : ℝ) ^ (-(j : ℝ) / 2)) = ENNReal.ofReal (2 * S) * (3 : ℝ≥0∞) ^ (-(j : ℝ) / 2) := by
  rw [ENNReal.ofReal_mul (by positivity : 0≤2*S),weightedEnergy_ofReal_three_rpow]

theorem weightedEnergy_combine_three (w v : ℝ≥0∞) (a b c z : ℝ) : w * (3 : ℝ≥0∞) ^ a * ((3 : ℝ≥0∞) ^ b) ^ c * (v * (3 : ℝ≥0∞) ^ z) = (w * v) * (3 : ℝ≥0∞) ^ (a + b * c + z) := by
  rw [← ENNReal.rpow_mul]
  have h : w * (3:ℝ≥0∞)^a * (3:ℝ≥0∞)^(b*c) * (v * (3:ℝ≥0∞)^z)
      = (w*v) * ((3:ℝ≥0∞)^a * (3:ℝ≥0∞)^(b*c) * (3:ℝ≥0∞)^z) := by
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [h, ← ENNReal.rpow_add a (b*c) (by norm_num) (by norm_num),
    ← ENNReal.rpow_add (a + b*c) z (by norm_num) (by norm_num)]

theorem weightedEnergy_three_mono (w : ℝ≥0∞) (a b : ℝ) (h : a ≤ b) : w * (3 : ℝ≥0∞) ^ a ≤ w * (3 : ℝ≥0∞) ^ b := by
  exact mul_le_mul_right (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) h) w

theorem weightedEnergy_three_split (j : ℕ) : (3 : ℝ≥0∞) ^ ((1 / 4 : ℝ) - (j : ℝ) / 4) = (3 : ℝ≥0∞) ^ (1 / 4 : ℝ) * (3 : ℝ≥0∞) ^ (-(j : ℝ) / 4) := by
  rw [show (1/4:ℝ)-(j:ℝ)/4=1/4+(-(j:ℝ)/4) by ring]
  exact ENNReal.rpow_add _ _ (by norm_num) (by norm_num)

theorem weightedEnergy_step_constant (K S p : ℝ) (hK : 0 ≤ K) (hS : 0 ≤ S) (hp : 0 < p) : ((ENNReal.ofReal K) ^ (1 / p) * ENNReal.ofReal (2 * S)) * (3 : ℝ≥0∞) ^ (1 / 4 : ℝ) = ENNReal.ofReal (2 * (3 : ℝ) ^ (1 / 4 : ℝ) * K ^ (1 / p) * S) := by
  rw [weightedEnergy_ofReal_K_rpow K p hK hp, ← weightedEnergy_ofReal_three_rpow]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hK _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem weightedEnergy_step_constant_pos : 0 < 2 * (3 : ℝ) ^ (1 / 4 : ℝ) := by
  positivity

theorem weightedEnergy_step_coeff_nonneg (K S p : ℝ) (hK : 0 ≤ K) (hS : 0 ≤ S) : 0 ≤ 2 * (3 : ℝ) ^ (1 / 4 : ℝ) * K ^ (1 / p) * S := by
  positivity

theorem weightedEnergy_step_bound {D p K S : ℝ} (hp : 0 < p) (hK : 0 ≤ K) (hS : 0 ≤ S) (hb : -(1 / 2 : ℝ) + D * (1 / 2 - 1 / p) + 3 / (8 * p) ≤ -(1 / 4 : ℝ)) (j : ℕ) : (ENNReal.ofReal K) ^ (1 / p) * (3 : ℝ≥0∞) ^ ((3 / 8 : ℝ) * ((j : ℝ) + 1) / p) * ((3 : ℝ≥0∞) ^ (D * ((j : ℝ) + 1))) ^ (1 / 2 - 1 / p) * ENNReal.ofReal (2 * S * (3 : ℝ) ^ (-(j : ℝ) / 2)) ≤ ENNReal.ofReal (2 * (3 : ℝ) ^ (1 / 4 : ℝ) * K ^ (1 / p) * S) * (3 : ℝ≥0∞) ^ (-(j : ℝ) / 4) := by
  rw [weightedEnergy_density_factor S hS j, weightedEnergy_combine_three]
  have he := weightedEnergy_step_exponent hb j
  calc _ ≤ _ := weightedEnergy_three_mono _ _ _ (by convert he using 1; ring)
    _ = _ := by rw [weightedEnergy_three_split, ← mul_assoc,
        weightedEnergy_step_constant K S p hK hS hp]

theorem weightedEnergy_ratio_expand (k : ℝ≥0∞) (a b p : ℝ) (hp : 0 < p) : ((k * (3 : ℝ≥0∞) ^ a) / (3 : ℝ≥0∞) ^ b) ^ (1 / p) = (k ^ (1 / p) * ((3 : ℝ≥0∞) ^ a) ^ (1 / p)) / ((3 : ℝ≥0∞) ^ b) ^ (1 / p) := by
  have hr : (0:ℝ) ≤ 1 / p := le_of_lt (one_div_pos.mpr hp)
  rw [ENNReal.div_rpow_of_nonneg _ _ hr, ENNReal.mul_rpow_of_nonneg _ _ hr]

theorem weightedEnergy_ratio_collect (k X Y Z : ℝ≥0∞) : (k * X / Y) * Z = (k * X) * (Z / Y) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

theorem weightedEnergy_threepow_ne_zero (b : ℝ) : (3 : ℝ≥0∞) ^ b ≠ 0 := by
  exact ne_of_gt (ENNReal.rpow_pos (by norm_num : (0:ℝ≥0∞)<3) (by norm_num : (3:ℝ≥0∞)≠⊤))

theorem weightedEnergy_threepow_ne_top (b : ℝ) : (3 : ℝ≥0∞) ^ b ≠ ⊤ := by
  exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num : (3:ℝ≥0∞)≠0) (by norm_num : (3:ℝ≥0∞)≠⊤)

theorem weightedEnergy_ratio_quotient (b p : ℝ) : ((3 : ℝ≥0∞) ^ b) ^ (1 / 2 : ℝ) / ((3 : ℝ≥0∞) ^ b) ^ (1 / p) = ((3 : ℝ≥0∞) ^ b) ^ (1 / 2 - 1 / p) := by
  have h0 := weightedEnergy_threepow_ne_zero b
  have htop := weightedEnergy_threepow_ne_top b
  exact (ENNReal.rpow_sub (1 / 2) (1 / p) h0 htop).symm

theorem weightedEnergy_ratio_power (a p : ℝ) : ((3 : ℝ≥0∞) ^ a) ^ (1 / p) = (3 : ℝ≥0∞) ^ (a / p) := by
  rw [← ENNReal.rpow_mul, show a * (1 / p) = a / p by ring]

theorem weightedEnergy_ratio_powers (k : ℝ≥0∞) (a b p : ℝ) (hp : 0 < p) : ((k * (3 : ℝ≥0∞) ^ a) / (3 : ℝ≥0∞) ^ b) ^ (1 / p) * ((3 : ℝ≥0∞) ^ b) ^ (1 / 2 : ℝ) = k ^ (1 / p) * (3 : ℝ≥0∞) ^ (a / p) * ((3 : ℝ≥0∞) ^ b) ^ (1 / 2 - 1 / p) := by
  rw [weightedEnergy_ratio_expand _ _ _ _ hp, weightedEnergy_ratio_collect,
    weightedEnergy_ratio_quotient, weightedEnergy_ratio_power]


theorem weightedEnergy_step_ratio_bound {D p K S : ℝ} (hp : 0 < p)
    (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hb : -(1 / 2 : ℝ) + D * (1 / 2 - 1 / p) + 3 / (8 * p) ≤ -(1 / 4 : ℝ))
    (j : ℕ) :
    ((ENNReal.ofReal K * (3 : ℝ≥0∞) ^ ((3 / 8 : ℝ) * ((j : ℝ) + 1))) /
        (3 : ℝ≥0∞) ^ (D * ((j : ℝ) + 1))) ^ (1 / p) *
      ((3 : ℝ≥0∞) ^ (D * ((j : ℝ) + 1))) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal (2 * S * (3 : ℝ) ^ (-(j : ℝ) / 2)) ≤
    ENNReal.ofReal (2 * (3 : ℝ) ^ (1 / 4 : ℝ) * K ^ (1 / p) * S) *
      (3 : ℝ≥0∞) ^ (-(j : ℝ) / 4) := by
  rw [weightedEnergy_ratio_powers _ _ _ _ hp]
  exact weightedEnergy_step_bound hp hK hS hb j

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy

