module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- Choose one disorder threshold for both point-factor moment rates. -/
theorem lem_as_coarse_shallow_grid_disorder_rate
    (q eta Rp Ri : ℝ)
    (hq : 1 ≤ q) (heta : 0 < eta) (hRp : 0 < Rp) (hRi : 0 < Ri) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ delta0 →
        Rp * ((2*q)+(2*q)^2) * delta^2 ≤
          (2*q) * eta * Real.log 3 ∧
        Ri * ((2*q)+(2*q)^2) * delta^2 ≤
          (2*q) * eta * Real.log 3 := by
  let A : ℝ := (2*q)+(2*q)^2
  let T : ℝ := (2*q) * eta * Real.log 3
  let D : ℝ := 1 + (Rp+Ri)*A
  have hA : 0 < A := by dsimp [A]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  let delta0 : ℝ := min 1 (T / D)
  have hd0 : 0 < delta0 := lt_min zero_lt_one (div_pos hT hD)
  have hd01 : delta0 ≤ 1 := min_le_left _ _
  have hd0T : delta0 ≤ T / D := min_le_right _ _
  refine ⟨delta0, hd0, hd01, ?_⟩
  intro delta hdelta hle
  have hδ1 : delta ≤ 1 := hle.trans hd01
  have hsq : delta^2 ≤ delta0 := by nlinarith
  have hDA : Rp*A ≤ D ∧ Ri*A ≤ D := by
    dsimp [D]
    constructor <;> nlinarith [mul_pos hRi hA, mul_pos hRp hA]
  have hDδ : D * delta0 ≤ T := by
    exact (mul_le_mul_of_nonneg_left hd0T hD.le).trans_eq
      (mul_div_cancel₀ T hD.ne')
  have hRpA : 0 ≤ Rp*A := mul_nonneg hRp.le hA.le
  have hRiA : 0 ≤ Ri*A := mul_nonneg hRi.le hA.le
  constructor
  · change Rp*A*delta^2 ≤ T
    calc
      Rp*A*delta^2 ≤ Rp*A*delta0 := mul_le_mul_of_nonneg_left hsq hRpA
      _ ≤ D*delta0 := mul_le_mul_of_nonneg_right hDA.1 hd0.le
      _ ≤ T := hDδ
  · change Ri*A*delta^2 ≤ T
    calc
      Ri*A*delta^2 ≤ Ri*A*delta0 := mul_le_mul_of_nonneg_left hsq hRiA
      _ ≤ D*delta0 := mul_le_mul_of_nonneg_right hDA.2 hd0.le
      _ ≤ T := hDδ

end Paper

