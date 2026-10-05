module

public import SubdiffusiveProcess.Analysis.PolynomialGeometricTail

@[expose] public section

/-! The affine spatial-cell cost in an initial-layer moment is absorbed by
half its triadic decay. This is a deterministic scalar estimate.
-/
namespace SubdiffusiveProcess

/-- The explicit initial-layer affine prefactor has a uniform geometric majorant. -/
theorem exists_initial_layer_half_decay (d : ℕ) (sigma s : ℝ)
    (hsigma : 0 ≤ sigma) (hs : 0 < s) :
    ∃ T : ℝ, 0 < T ∧ ∀ k : ℕ,
      (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (sigma *
        (2 * (2 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3))) ≤
        T * (3 : ℝ) ^ (-(s / 16) * (k : ℝ)) := by
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  let C0 : ℝ := 1 + 2 * sigma * (2 + ((d : ℝ) + 1) * Real.log 3)
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  obtain ⟨C, hC, hbound⟩ := exists_polynomial_triadic_half_decay_bound 1 (s / 8) (by positivity)
  refine ⟨C0 * C, mul_pos hC0 hC, ?_⟩
  intro k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpoly : sigma * (2 * (2 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3)) ≤
      C0 * ((k : ℝ) + 1) := by
    have hbase : 2 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3 ≤
        (2 + ((d : ℝ) + 1) * Real.log 3) * ((k : ℝ) + 1) := by
      push_cast
      nlinarith only [hk, mul_nonneg hk hlog]
    have hh := mul_le_mul_of_nonneg_left hbase (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hsigma)
    dsimp only [C0]
    nlinarith only [hh, hk]
  have hdecay : ((k : ℝ) + 1) * (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) ≤
      C * (3 : ℝ) ^ (-(s / 16) * (k : ℝ)) := by
    have hb := hbound k
    rw [pow_one, show -((s / 8) / 2) = -(s / 16) by ring] at hb
    exact hb
  have hfirst := mul_le_mul_of_nonneg_left hpoly
    (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (-(s / 8) * (k : ℝ)))
  have hlast := mul_le_mul_of_nonneg_left hdecay hC0.le
  nlinarith only [hfirst, hlast]

end SubdiffusiveProcess
