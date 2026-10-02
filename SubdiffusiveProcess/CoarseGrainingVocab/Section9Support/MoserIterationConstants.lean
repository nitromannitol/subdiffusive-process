import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The convergent product in Moser iteration

The exponent `chi` is any real number greater than one. A coefficient
`8 C (2 chi)^n` in the power inequality produces a uniformly bounded product,
since `sum (n+1) / chi^n` converges. All constants precede the norm sequence.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal NNReal BigOperators
open Filter
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Uniform bound for the full product of constants along geometrically shrinking cubes. -/
theorem exists_moser_iteration_constant {chi C : ℝ} (hchi : 1 < chi) (hC : 0 < C) :
    ∃ B : ℝ, 0 < B ∧
      ∀ N : ℕ → ℝ≥0∞,
        (∀ n, N (n + 1) ^ (chi ^ n) ≤
          ENNReal.ofReal (8 * C * (2 * chi) ^ n) * N n ^ (chi ^ n)) →
        ∀ n, N n ≤ ENNReal.ofReal B * N 0 := by
  have hchi0 : 0 < chi := by linarith
  let D : ℝ := max 1 (max (8 * C) (2 * chi))
  have hD1 : 1 ≤ D := le_max_left _ _
  have hCD : 8 * C ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hD0 : 0 < D := (mul_pos (by norm_num : (0 : ℝ) < 8) hC).trans_le hCD
  have hchiD : 2 * chi ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  let b : ℕ → ℝ := fun n => ((n : ℝ) + 1) / chi ^ n
  have hb0 (n : ℕ) : 0 ≤ b n := by dsimp only [b]; positivity
  have hnorm : ‖chi⁻¹‖ < 1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hchi0.le)]
    exact (inv_lt_one₀ hchi0).mpr hchi
  have hsum : Summable b := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    have h0 := summable_geometric_of_norm_lt_one hnorm
    simpa only [b, pow_one, add_mul, one_mul, div_eq_mul_inv, inv_pow] using h1.add h0
  let S : ℝ := ∑' n, b n
  refine ⟨D ^ S, Real.rpow_pos_of_pos hD0 _, ?_⟩
  intro N hN n
  have hcoef (k : ℕ) : 8 * C * (2 * chi) ^ k ≤ D ^ (k + 1) := by
    rw [pow_succ']
    exact mul_le_mul hCD (pow_le_pow_left₀ (by positivity) hchiD k)
      (by positivity) hD0.le
  have hstep (k : ℕ) : N (k + 1) ≤ ENNReal.ofReal (D ^ b k) * N k := by
    have hk0 : 0 < chi ^ k := pow_pos hchi0 k
    have h := (hN k).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hcoef k)) le_rfl)
    have hr := ENNReal.rpow_le_rpow h (inv_nonneg.mpr hk0.le)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hk0.le),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_inv_cancel₀ hk0.ne', ENNReal.rpow_one] at hr
    have hDpow : (ENNReal.ofReal (D ^ (k + 1))) ^ (chi ^ k)⁻¹ =
        ENNReal.ofReal (D ^ b k) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hD0.le _) (inv_nonneg.mpr hk0.le),
        ← Real.rpow_natCast D (k + 1), ← Real.rpow_mul hD0.le]
      simp only [b, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
    simpa only [hDpow, ENNReal.rpow_one] using hr
  have hfinite (k : ℕ) : N k ≤ ENNReal.ofReal (D ^ (∑ j ∈ Finset.range k, b j)) * N 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      refine (hstep k).trans ((mul_le_mul' le_rfl ih).trans_eq ?_)
      rw [Finset.sum_range_succ, Real.rpow_add hD0,
        ENNReal.ofReal_mul (Real.rpow_nonneg hD0.le _)]
      ring
  refine (hfinite n).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  exact Real.rpow_le_rpow_of_exponent_le hD1 (hsum.sum_le_tsum (Finset.range n) (fun k _ => hb0 k))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
