module

public import Mathlib.Tactic

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

theorem reversible_drift_le_quadratic {d r C g : ℝ}
    (hd : 0 ≤ d) (hr : 0 ≤ r) (hC : 0 ≤ C) (hg : g ≤ C * (1 + r)) :
    2 * d + 2 * r * g ≤ (2 * d + 4 * C) * (1 + r ^ 2) := by
  have h2 : 2 * r * g ≤ 2 * r * (C * (1 + r)) :=
    mul_le_mul_of_nonneg_left hg (by positivity)
  have h3 : 2 * r * (1 + r) ≤ 4 * (1 + r ^ 2) := by
    nlinarith [sq_nonneg (r - 1), hr]
  have h4 : 2 * r * (C * (1 + r)) ≤ C * (4 * (1 + r ^ 2)) := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hC]
  have key : 2 * r * g ≤ 4 * C * (1 + r ^ 2) := by
    nlinarith [h2, h4]
  have h5 : 0 ≤ 2 * d * r ^ 2 := mul_nonneg (by positivity) (sq_nonneg r)
  nlinarith [key, h5]

theorem divergence_drift_le_quadratic {d r C b g : ℝ}
    (hd : 0 ≤ d) (hr : 0 ≤ r) (hC : 0 ≤ C) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hbg : b + g ≤ C * (1 + r)) :
    2 * d * b + 2 * r * g ≤ 4 * (d + 1) * C * (1 + r ^ 2) := by
  have hb1 : b ≤ C * (1 + r) := by linarith
  have hg1 : g ≤ C * (1 + r) := by linarith
  have h1 : 2 * d * b ≤ 2 * d * (C * (1 + r)) :=
    mul_le_mul_of_nonneg_left hb1 (by positivity)
  have h2 : 2 * r * g ≤ 2 * r * (C * (1 + r)) :=
    mul_le_mul_of_nonneg_left hg1 (by positivity)
  have h3 : d + r ≤ (d + 1) * (1 + r) := by
    linarith [mul_nonneg hd hr]
  have h4 : 2 * d * (C * (1 + r)) + 2 * r * (C * (1 + r))
      ≤ 2 * (C * (1 + r)) * ((d + 1) * (1 + r)) := by
    have hpos : 0 ≤ 2 * (C * (1 + r)) := by positivity
    have key := mul_le_mul_of_nonneg_left h3 hpos
    nlinarith [key]
  have h5 : (1 + r) ^ 2 ≤ 2 * (1 + r ^ 2) := by
    linarith [sq_nonneg (r - 1)]
  have h6 : 2 * (C * (1 + r)) * ((d + 1) * (1 + r))
      ≤ 4 * (d + 1) * C * (1 + r ^ 2) := by
    have hCpos : 0 ≤ 2 * (d + 1) * C := by positivity
    have key := mul_le_mul_of_nonneg_left h5 hCpos
    nlinarith [key]
  nlinarith [h1, h2, h4, h6]

theorem weighted_drift_scale_cancel {s b v : ℝ} (hs : s ≠ 0) :
    (s * b)⁻¹ * (s * v) = b⁻¹ * v := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp [hs, hb]

theorem radial_flux_lower_bound {P PP b s q beta D C V G B rho : ℝ}
    (hP : P * s = -(beta / 2) * b) (hPP : 0 ≤ PP)
    (hb : 0 ≤ b) (hs : 0 < s) (hq : 0 ≤ q) (hbeta : 0 ≤ beta)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hV : V ≤ G)
    (hkey : beta * (G + D * C) ≤ B * rho * s) :
    -(B * rho * b) ≤ 2 * P * V + C * (4 * q * PP + 2 * D * P) := by
  have _ := hD
  have h1 : beta * b * V ≤ beta * b * G :=
    mul_le_mul_of_nonneg_left hV (mul_nonneg hbeta hb)
  have hkeyb : beta * (G + D * C) * b ≤ B * rho * s * b :=
    mul_le_mul_of_nonneg_right hkey hb
  have hnn : 0 ≤ 4 * C * q * PP * s := by positivity
  have hscaled : 0 ≤ (2 * P * V + C * (4 * q * PP + 2 * D * P) + B * rho * b) * s := by
    have hX : (2 * P * V + C * (4 * q * PP + 2 * D * P) + B * rho * b) * s
        = -beta * V * b - C * D * beta * b + 4 * C * q * PP * s + B * rho * b * s := by
      linear_combination (2 * V + 2 * C * D) * hP
    rw [hX]
    nlinarith [hkeyb, h1, hnn]
  have hfin : (0 : ℝ) * s ≤ 2 * P * V + C * (4 * q * PP + 2 * D * P) + B * rho * b :=
    le_of_mul_le_mul_right (by simpa using hscaled) hs
  linarith

theorem radial_growth_scalar_bound {E G C n K rho s S D : ℝ}
    (hG : 0 ≤ G) (hC : 0 ≤ C) (hn : 0 ≤ n) (hK : 0 ≤ K)
    (hrho : 0 ≤ rho) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hE : E ≤ S * n) (hgrowth : G + C ≤ K * rho * (1 + n))
    (hs : 1 + n ^ 2 ≤ s) :
    E * G + D * C ≤ (2 * S + 2 * D) * K * rho * s := by
  have hGle : G ≤ K * rho * (1 + n) :=
    le_trans (le_add_of_nonneg_right hC) hgrowth
  have hCle : C ≤ K * rho * (1 + n) :=
    le_trans (le_add_of_nonneg_left hG) hgrowth
  have hs1 : 1 ≤ s := by linarith [hs, sq_nonneg n]
  have h2n : 2 * n ≤ 1 + n ^ 2 := by
    have h1 : 0 ≤ (n - 1) ^ 2 := sq_nonneg (n - 1)
    have h2 : (n - 1) ^ 2 = n ^ 2 - 2 * n + 1 := by ring
    linarith
  have hm1 : n * (1 + n) ≤ 2 * s := by nlinarith [h2n, hs, hs1]
  have hm2 : 1 + n ≤ 2 * s := by nlinarith [h2n, hs, sq_nonneg n]
  have hSn : 0 ≤ S * K * rho := mul_nonneg (mul_nonneg hS hK) hrho
  have hDr : 0 ≤ D * K * rho := mul_nonneg (mul_nonneg hD hK) hrho
  have hEG : E * G ≤ 2 * S * K * rho * s := by
    calc E * G ≤ S * n * G := mul_le_mul_of_nonneg_right hE hG
      _ ≤ S * n * (K * rho * (1 + n)) :=
          mul_le_mul_of_nonneg_left hGle (mul_nonneg hS hn)
      _ = S * K * rho * (n * (1 + n)) := by ring
      _ ≤ S * K * rho * (2 * s) := mul_le_mul_of_nonneg_left hm1 hSn
      _ = 2 * S * K * rho * s := by ring
  have hDC : D * C ≤ 2 * D * K * rho * s := by
    calc D * C ≤ D * (K * rho * (1 + n)) := mul_le_mul_of_nonneg_left hCle hD
      _ = D * K * rho * (1 + n) := by ring
      _ ≤ D * K * rho * (2 * s) := mul_le_mul_of_nonneg_left hm2 hDr
      _ = 2 * D * K * rho * s := by ring
  calc E * G + D * C
      ≤ 2 * S * K * rho * s + 2 * D * K * rho * s := by linarith [hEG, hDC]
    _ = (2 * S + 2 * D) * K * rho * s := by ring

theorem abs_div_le_sum_bounds {a b rho w v : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hrho : 0 < rho) (hw : 0 ≤ w)
    (hlow : -(a * rho * w) ≤ v) (hupp : v ≤ b * rho * w) :
    |v / rho| ≤ (a + b) * w := by
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hrho]
    have h1 : 0 ≤ b * rho * w := mul_nonneg (mul_nonneg hb hrho.le) hw
    nlinarith [hlow, h1]
  · rw [div_le_iff₀ hrho]
    have h2 : 0 ≤ a * rho * w := mul_nonneg (mul_nonneg ha hrho.le) hw
    nlinarith [hupp, h2]

theorem reciprocalNatSucc_pos_le_one (n : ℕ) :
    0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := by
  constructor
  · positivity
  · have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hn

theorem abs_quadratic_drift_scalar {d r b g K z : ℝ}
    (hd : 0 ≤ d) (hr : 0 ≤ r) (hb : 0 ≤ b) (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hbg : b + g ≤ K * (1 + r)) (hz : |z| ≤ r * g) :
    |2*d*b + 2*z| ≤ 4*(d+1)*K*(1+r^2) := by
  have hbK : b ≤ K * (1 + r) := le_trans (le_add_of_nonneg_right hg) hbg
  have hgK : g ≤ K * (1 + r) := le_trans (le_add_of_nonneg_left hb) hbg
  have hr1 : r ≤ 1 + r^2 := by
    nlinarith [sq_nonneg (r - 1)]
  have h2 : (1:ℝ) + r ≤ 2 * (1 + r^2) := by
    nlinarith [sq_nonneg (r - 1)]
  have hK2 : K * (1 + r) ≤ 2 * K * (1 + r^2) := by
    nlinarith [h2, hK]
  have hb2 : b ≤ 2 * K * (1 + r^2) := le_trans hbK hK2
  have hdb : d * b ≤ 2 * d * K * (1 + r^2) := by
    nlinarith [hb2]
  have hrg : r * g ≤ K * r + K * r^2 := by
    nlinarith [hgK]
  have hKr : K * r ≤ K * (1 + r^2) := by
    nlinarith
  have e2 : |2*d*b| = 2*d*b := abs_of_nonneg (by nlinarith)
  have e3 : |2*z| = 2*|z| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  calc |2*d*b + 2*z| ≤ |2*d*b| + |2*z| := abs_add_le _ _
    _ = 2*d*b + 2*|z| := by rw [e2, e3]
    _ ≤ 2*d*b + 2*r*g := by nlinarith [hz]
    _ ≤ 4*(d+1)*K*(1+r^2) := by nlinarith [hdb, hrg, hKr]

theorem abs_quadratic_drift_weighted_scalar {d r b g K rho z : ℝ}
    (hd : 0 ≤ d) (hr : 0 ≤ r) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hK : 0 ≤ K) (hrho : 0 < rho) (hbg : b+g ≤ K*rho*(1+r))
    (hz : |z| ≤ r*g) :
    |(2*d*b+2*z)/rho| ≤ 4*(d+1)*K*(1+r^2) := by
  have h1 : b/rho + g/rho ≤ K*(1+r) := by
    rw [← add_div, div_le_iff₀ hrho]
    nlinarith [hbg]
  have h2 : |z/rho| ≤ r*(g/rho) := by
    rw [abs_div, abs_of_pos hrho, div_le_iff₀ hrho]
    have hr' : r*(g/rho)*rho = r*g := by field_simp
    rw [hr']
    exact hz
  have key := abs_quadratic_drift_scalar hd hr (div_nonneg hb hrho.le)
    (div_nonneg hg hrho.le) hK h1 h2
  simpa only [div_eq_mul_inv, add_mul, mul_assoc] using key

theorem coefficient_ratio_le_quadratic_scalar {b g K rho n q : ℝ}
    (hg : 0 ≤ g) (hK : 0 ≤ K) (hrho : 0 < rho) (hn : 0 ≤ n)
    (hsq : n^2 ≤ q) (hbg : g+b ≤ K*rho*(1+n)) :
    b/rho ≤ 2*K*(1+q) := by
  have _ := hn
  have h1 : 1 + n ≤ 2 * (1 + q) := by
    nlinarith [sq_nonneg (n - 1), hsq, hn]
  have h2 : b ≤ K * rho * (1 + n) := by
    linarith
  have h3 : b ≤ K * rho * (2 * (1 + q)) := by
    exact h2.trans (mul_le_mul_of_nonneg_left h1 (mul_nonneg hK hrho.le))
  rw [div_le_iff₀ hrho]
  nlinarith [h3]

theorem one_add_add_sq_le (a r : ℝ) :
    1+(a+r)^2 ≤ 2*(1+a^2+r^2) := by
  nlinarith [sq_nonneg (a-r)]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
