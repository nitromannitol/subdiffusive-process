module

public import SubdiffusiveProcess.Static.GridMassGeometry

@[expose] public section

/-! # The half-power mesh weight and deterministic mass growth constants -/
noncomputable section
namespace SubdiffusiveProcess.Static

/-- A single deterministic constant pays for the inner and outer cube sides. -/
def massGrowthConstant (d : ℕ) : ℝ := (3 : ℝ) ^ ((d : ℝ) + 1 / 2) + (27 : ℝ) ^ d + 1

theorem one_le_massGrowthConstant (d : ℕ) : 1 ≤ massGrowthConstant d := by
  unfold massGrowthConstant
  linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((d : ℝ) + 1 / 2),
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 27) d]

theorem massGrowthConstant_pos (d : ℕ) : 0 < massGrowthConstant d :=
  zero_lt_one.trans_le (one_le_massGrowthConstant d)

/-- The mesh envelope weight is exactly the inverse square root of its side. -/
theorem triadic_mesh_weight (n : ℕ) :
    (3 : ℝ) ^ ((1 / 2 : ℝ) * n) = (((3 : ℝ) ^ n)⁻¹) ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- Converting the two cube tests to the desired two real-radius powers. -/
theorem mass_growth_numeric {d : ℕ} (hd : 1 ≤ d) {r h W a b : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hW : 0 < W) (ha : 0 < a)
    (hrh : r ≤ 3 * h) (hhr : h ≤ r)
    (hai : a⁻¹ ≤ W * h ^ (-(1 / 2 : ℝ)))
    (hb : b ≤ W * h ^ (-(1 / 2 : ℝ))) :
    (massGrowthConstant d * W)⁻¹ * r ^ ((d : ℝ) + 1 / 2) ≤ h ^ d * a ∧
      (27 * h) ^ d * b ≤ (massGrowthConstant d * W) * r ^ ((d : ℝ) - 1 / 2) := by
  have hG := massGrowthConstant_pos d
  have hD : 0 ≤ (d : ℝ) - 1 / 2 := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hLo : (3 : ℝ) ^ ((d : ℝ) + 1 / 2) ≤ massGrowthConstant d := by
    unfold massGrowthConstant
    linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((d : ℝ) + 1 / 2),
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 27) d]
  have hUp : (27 : ℝ) ^ d ≤ massGrowthConstant d := by
    unfold massGrowthConstant
    linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((d : ℝ) + 1 / 2),
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 27) d]
  have hcancel : h ^ (-(1 / 2 : ℝ)) * h ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hh]
    simp
  have hhalf : h ^ (1 / 2 : ℝ) ≤ W * a := by
    have hprod : 1 ≤ (W * h ^ (-(1 / 2 : ℝ))) * a := by
      have hm := mul_le_mul_of_nonneg_right hai ha.le
      simpa only [inv_mul_cancel₀ ha.ne'] using hm
    have hm := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hh.le (1 / 2 : ℝ))
    rw [show (W * h ^ (-(1 / 2 : ℝ))) * a * h ^ (1 / 2 : ℝ) =
      (W * a) * (h ^ (-(1 / 2 : ℝ)) * h ^ (1 / 2 : ℝ)) by ring,
      hcancel, mul_one, one_mul] at hm
    exact hm
  constructor
  · rw [inv_mul_eq_div]
    apply (div_le_iff₀ (mul_pos hG hW)).mpr
    calc
      r ^ ((d : ℝ) + 1 / 2) ≤ (3 * h) ^ ((d : ℝ) + 1 / 2) :=
        Real.rpow_le_rpow hr.le hrh (by positivity)
      _ = (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * h ^ ((d : ℝ) + 1 / 2) :=
        Real.mul_rpow (by norm_num) hh.le
      _ ≤ massGrowthConstant d * h ^ ((d : ℝ) + 1 / 2) :=
        mul_le_mul_of_nonneg_right hLo (by positivity)
      _ = massGrowthConstant d * (h ^ d * h ^ (1 / 2 : ℝ)) := by
        rw [Real.rpow_add hh, Real.rpow_natCast]
      _ ≤ massGrowthConstant d * (h ^ d * (W * a)) := by gcongr
      _ = _ := by ring
  · calc
      (27 * h) ^ d * b ≤ (27 * h) ^ d * (W * h ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (27 : ℝ) ^ d * W * h ^ ((d : ℝ) - 1 / 2) := by
        rw [mul_pow, ← Real.rpow_natCast h d, Real.rpow_sub hh]
        rw [Real.rpow_neg hh.le]
        ring
      _ ≤ massGrowthConstant d * W * r ^ ((d : ℝ) - 1 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hUp hW.le)
          (Real.rpow_le_rpow hh.le hhr hD) (by positivity) (by positivity)
      _ = _ := rfl

end SubdiffusiveProcess.Static
