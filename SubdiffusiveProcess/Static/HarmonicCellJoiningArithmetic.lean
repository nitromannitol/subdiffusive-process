import SubdiffusiveProcess.Static.HarmonicCellMomentArithmetic

/-! # Exact exponent margin and microscopic scalar-price arithmetic -/

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The local reflected L² price retains precisely the quarter-power
margin between the macroscopic and microscopic energy exponents. -/
theorem harmonicCell_radius_margin (d : ℕ) {eps T : ℝ} (heps : 0 < eps) (hT : 0 < T) :
    (eps / T) ^ (1 / 2 : ℝ) * (((eps / T) ^ d)⁻¹ * eps ^ ((d : ℝ) - 1 / 4)) =
      eps ^ (1 / 4 : ℝ) * T ^ ((d : ℝ) - 1 / 2) := by
  have hrho := div_pos heps hT
  rw [← Real.rpow_natCast, ← Real.rpow_neg hrho.le]
  rw [← mul_assoc, ← Real.rpow_add hrho]
  rw [Real.div_rpow heps.le hT.le, div_eq_mul_inv, ← Real.rpow_neg hT.le]
  have hexp : 1 / 2 + -(d : ℝ) = -((d : ℝ) - 1 / 2) := by ring
  rw [hexp, mul_assoc, mul_comm (T ^ (- -((d : ℝ) - 1 / 2))), ← mul_assoc,
    ← Real.rpow_add heps]
  congr 1 <;> ring

/-- A bounded datum's volume term has a stronger margin. -/
theorem harmonicCell_sqrt_radius_le_margin {eps T : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hT : 1 ≤ T) :
    (eps / T) ^ (1 / 2 : ℝ) ≤ eps ^ (1 / 4 : ℝ) := by
  have hT0 := zero_lt_one.trans_le hT
  calc
    _ ≤ eps ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (div_pos heps hT0).le
      ((div_le_iff₀ hT0).mpr (by nlinarith)) (by norm_num)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge heps heps1 (by norm_num)

/-- The square of the native data price is controlled directly by the
energy budget and bounded forcing. -/
theorem harmonicCell_sqrt_price_sq_le {A J : ℝ} (hA : 0 ≤ A) :
    (Real.sqrt A + J) ^ 2 ≤ 2 * (A + J ^ 2) := by
  nlinarith [Real.sq_sqrt hA, sq_nonneg (Real.sqrt A - J)]

/-- Subunit macroscopic growth above the microscopic transition needs no
coefficient-envelope factor. -/
theorem harmonicCell_large_radius_power_le {d : ℕ} {eps r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hepsr : eps ≤ r) :
    (max r eps) ^ ((d : ℝ) - 1 / 4) ≤ r ^ ((d : ℝ) - 1 / 2) := by
  rw [max_eq_left hepsr]
  exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)

/-- Between the microscopic transition and physical radius one, the
macroscopic budget pays only the quarter-power margin. -/
theorem harmonicCell_transition_power_le (d : ℕ) (hd : 1 ≤ d)
    {eps T r : ℝ} (heps : 0 < eps) (hT : 0 < T) (hr : 0 < r)
    (hrsmall : r ≤ eps) (hrtransition : eps / T ≤ r) :
    (max r eps) ^ ((d : ℝ) - 1 / 4) ≤
      eps ^ (1 / 4 : ℝ) * T ^ ((d : ℝ) - 1 / 2) * r ^ ((d : ℝ) - 1 / 2) := by
  have ht : 0 ≤ (d : ℝ) - 1 / 2 := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [max_eq_right hrsmall]
  have hR := Real.rpow_le_rpow (div_pos heps hT).le hrtransition ht
  have heq : eps ^ ((d : ℝ) - 1 / 4) =
      eps ^ (1 / 4 : ℝ) * T ^ ((d : ℝ) - 1 / 2) * (eps / T) ^ ((d : ℝ) - 1 / 2) := by
    have hepspow : eps ^ ((d : ℝ) - 1 / 4) =
        eps ^ (1 / 4 : ℝ) * eps ^ ((d : ℝ) - 1 / 2) := by
      rw [← Real.rpow_add heps]
      congr 1
      ring
    rw [hepspow, Real.div_rpow heps.le hT.le]
    field_simp [(Real.rpow_pos_of_pos hT ((d : ℝ) - 1 / 2)).ne']
  rw [heq]
  exact mul_le_mul_of_nonneg_left hR (by positivity)

end SubdiffusiveProcess.Static
