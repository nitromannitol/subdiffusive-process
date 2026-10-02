import SubdiffusiveProcess.Analysis.SubwavelengthAbsorption

/-! An exponent gap absorbs a cutoff envelope in triadic oscillation bounds.
This scalar estimate contains no regularity hypothesis or probabilistic assertion. -/
namespace SubdiffusiveProcess

/-- A stronger grid exponent absorbs the corresponding cutoff growth below the cutoff. -/
theorem grid_oscillation_absorb (K B D alpha beta : ℝ) (N k : ℕ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hab : alpha ≤ beta) (hNk : N ≤ k)
    (hK : K ≤ B*(3:ℝ)^((beta-alpha)*N)) :
    K*(D*(3:ℝ)^(-(k:ℤ)))^beta ≤ D^beta*B*(3:ℝ)^(-(alpha*k)) := by
  have hr : (0:ℝ) < (3:ℝ)^(-(k:ℤ)) := by positivity
  have hrN : (3:ℝ)^(-(k:ℤ)) ≤ (3:ℝ)^(-(N:ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hh := subwavelength_rpow_absorb K B (beta-alpha) ((3:ℝ)^(-(k:ℤ))) N
    hB (sub_nonneg.mpr hab) hr hrN hK
  have ha : ((3:ℝ)^(-(k:ℤ)))^alpha = (3:ℝ)^(-(alpha*k)) := by
    rw [← Real.rpow_intCast,← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have hid : K*(D*(3:ℝ)^(-(k:ℤ)))^beta =
      D^beta*(K*((3:ℝ)^(-(k:ℤ)))^(beta-alpha))*((3:ℝ)^(-(k:ℤ)))^alpha := by
    rw [Real.mul_rpow hD hr.le]
    rw [mul_assoc (D^beta),mul_assoc K,← Real.rpow_add hr,sub_add_cancel]
    ring
  rw [hid,ha]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hD _)) (by positivity)

end SubdiffusiveProcess
