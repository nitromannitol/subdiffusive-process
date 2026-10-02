import SubdiffusiveProcess.Static.HarmonicCellMicroscopicPrice

/-! # Smooth and transition scalar bounds for harmonic cell joining -/
noncomputable section
namespace SubdiffusiveProcess.Static

theorem harmonicCell_smooth_price_le (d : ℕ) {eps T R G B r : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hT : 1 ≤ T) (hR : 1 ≤ R) (hG : 1 ≤ G)
    (hr : 0 < r) (hrho : r ≤ eps / T) :
    R * ((d : ℝ) * B) ^ 2 * (2 * r) ^ d ≤
      ((2 : ℝ) ^ d * (d : ℝ) ^ 2) * (eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d) *
        B ^ 2 * r ^ ((d : ℝ) - 1 / 2) := by
  have hroot : r ^ (1 / 2 : ℝ) ≤ eps ^ (1 / 4 : ℝ) :=
    (Real.rpow_le_rpow hr.le hrho (by norm_num)).trans
      (harmonicCell_sqrt_radius_le_margin heps heps1 hT)
  have hR5 : R ≤ R ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hR (by norm_num : 1 ≤ 5)
  have hTd : 1 ≤ T ^ d := one_le_pow₀ hT
  have hscale : R * r ^ (1 / 2 : ℝ) ≤ eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d := by
    calc
      _ ≤ R ^ 5 * eps ^ (1 / 4 : ℝ) := by gcongr
      _ = eps ^ (1 / 4 : ℝ) * R ^ 5 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hpow : r ^ d = r ^ ((d : ℝ) - 1 / 2) * r ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    ring
  simp only [mul_pow]
  rw [hpow]
  have h := mul_le_mul_of_nonneg_right hscale
    (by positivity : 0 ≤ (2 : ℝ) ^ d * (d : ℝ) ^ 2 * B ^ 2 * r ^ ((d : ℝ) - 1 / 2))
  nlinarith only [h]

theorem harmonicCell_transition_price_le (d : ℕ) (hd : 1 ≤ d)
    {eps T R G r : ℝ} (heps : 0 < eps) (hT : 1 ≤ T) (hR : 1 ≤ R) (hG : 1 ≤ G)
    (hr : 0 < r) (hrsmall : r ≤ eps) (hrtransition : eps / T / (2 * (d : ℝ)) ≤ r) :
    G * (max r eps) ^ ((d : ℝ) - 1 / 4) ≤
      (2 * (d : ℝ)) ^ ((d : ℝ) - 1 / 2) *
        (eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d) * r ^ ((d : ℝ) - 1 / 2) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT0 := zero_lt_one.trans_le hT
  have hbase : 0 < 2 * (d : ℝ) := by linarith
  have htrans : eps / (2 * (d : ℝ) * T) ≤ r := by
    simpa only [div_div, mul_comm T] using hrtransition
  have hp := harmonicCell_transition_power_le d hd heps (by positivity) hr hrsmall htrans
  rw [Real.mul_rpow (by positivity : 0 ≤ 2 * (d : ℝ)) hT0.le] at hp
  have hTp : T ^ ((d : ℝ) - 1 / 2) ≤ T ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hR5 : 1 ≤ R ^ 5 := one_le_pow₀ hR
  calc
    _ ≤ G * (eps ^ (1 / 4 : ℝ) *
        ((2 * (d : ℝ)) ^ ((d : ℝ) - 1 / 2) * T ^ ((d : ℝ) - 1 / 2)) *
        r ^ ((d : ℝ) - 1 / 2)) := mul_le_mul_of_nonneg_left hp (by linarith)
    _ ≤ G * (eps ^ (1 / 4 : ℝ) *
        ((2 * (d : ℝ)) ^ ((d : ℝ) - 1 / 2) * T ^ d) *
        r ^ ((d : ℝ) - 1 / 2)) := by gcongr
    _ = (2 * (d : ℝ)) ^ ((d : ℝ) - 1 / 2) *
        (eps ^ (1 / 4 : ℝ) * 1 * G * T ^ d) * r ^ ((d : ℝ) - 1 / 2) := by ring
    _ ≤ _ := by gcongr

end SubdiffusiveProcess.Static
