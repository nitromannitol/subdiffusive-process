module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The discounted `j`-series for the `Psc` moment bound (pure real arithmetic)

With `R ≥ 1`, `32 (d+1) ≤ s R` and `16 R σ² ≤ s`, the `j`-th term
`(3^{-sj/8})^R 2^{R-1} ((2*3^{2j+1}+1)^d (2e^{R²σ²/4})^{2j+1} + C_B)` is at most
`K ρ^j` with `ρ ≤ 3^{-sR/32} < 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SubdiffusiveProcess.Paper

/-- The `j`-th term of the `Psc` moment series. -/
def aux_prefix_praw_term (d : ℕ) (s R σ CB : ℝ) (j : ℕ) : ℝ :=
  ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) ^ R *
    ((2 : ℝ) ^ (R - 1) *
      ((((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) *
        (Real.exp (R ^ 2 * σ ^ 2 / 4) * 2) ^ (2 * j + 1) + CB))

theorem aux_prefix_praw_term_nonneg (d : ℕ) (s R σ CB : ℝ) (hCB : 0 ≤ CB) (j : ℕ) :
    0 ≤ aux_prefix_praw_term d s R σ CB j := by
  unfold aux_prefix_praw_term
  have h1 : 0 ≤ ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) ^ R := by positivity
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (R - 1) := by positivity
  have h3 : (0 : ℝ) ≤ (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ (Real.exp (R ^ 2 * σ ^ 2 / 4) * 2) ^ (2 * j + 1) := by positivity
  positivity

theorem aux_prefix_praw_one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  linarith

theorem aux_prefix_praw_exp_le_three_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x ≤ (3 : ℝ) ^ x := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  refine Real.exp_le_exp.2 ?_
  have := aux_prefix_praw_one_lt_log_three
  nlinarith

/-- The geometric ratio is strictly below one. -/
theorem aux_prefix_praw_ratio_lt_one (d : ℕ) (s R σ : ℝ) (hs : 0 < s) (hR : 1 ≤ R)
    (hRs : 32 * ((d : ℝ) + 1) ≤ s * R) (hσ : 16 * R * σ ^ 2 ≤ s) :
    (3 : ℝ) ^ (-(s * R / 8)) * (9 : ℝ) ^ d * (Real.exp (R ^ 2 * σ ^ 2 / 4) * 2) ^ 2 < 1 := by
  have hsR : 0 < s * R := by positivity
  have hE : (Real.exp (R ^ 2 * σ ^ 2 / 4) * 2) ^ 2 = Real.exp (R ^ 2 * σ ^ 2 / 2) * 4 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num
    ring_nf
  have h1 : (9 : ℝ) ^ d * 4 ≤ (3 : ℝ) ^ (s * R / 16) := by
    have hle : (9 : ℝ) ^ d * 4 ≤ (3 : ℝ) ^ (((2 * d + 2 : ℕ)) : ℝ) := by
      rw [Real.rpow_natCast, pow_add, pow_mul]
      norm_num
    refine hle.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    push_cast
    linarith
  have h2 : Real.exp (R ^ 2 * σ ^ 2 / 2) ≤ (3 : ℝ) ^ (s * R / 32) := by
    have hx : R ^ 2 * σ ^ 2 / 2 ≤ s * R / 32 := by
      have hR0 : 0 ≤ R := by linarith
      have := mul_le_mul_of_nonneg_left hσ hR0
      nlinarith
    exact (Real.exp_le_exp.2 hx).trans (aux_prefix_praw_exp_le_three_rpow (by positivity))
  have h0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * R / 8)) := by positivity
  calc (3 : ℝ) ^ (-(s * R / 8)) * (9 : ℝ) ^ d * (Real.exp (R ^ 2 * σ ^ 2 / 4) * 2) ^ 2 =
        (3 : ℝ) ^ (-(s * R / 8)) * ((9 : ℝ) ^ d * 4) * Real.exp (R ^ 2 * σ ^ 2 / 2) := by
          rw [hE]; ring
    _ ≤ (3 : ℝ) ^ (-(s * R / 8)) * (3 : ℝ) ^ (s * R / 16) * (3 : ℝ) ^ (s * R / 32) := by
          gcongr
    _ = (3 : ℝ) ^ (-(s * R / 32)) := by
          rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
          congr 1
          ring
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The explicit geometric majorant of the `j`-th term. -/
theorem aux_prefix_praw_term_le_geom (d : ℕ) (s R σ CB : ℝ) (hCB : 0 ≤ CB) (j : ℕ) :
    aux_prefix_praw_term d s R σ CB j ≤
      ((2 : ℝ) ^ (R - 1) * ((9 : ℝ) ^ d * (Real.exp (R ^ 2 * σ ^ 2 / 4) * 2) + CB)) *
        ((3 : ℝ) ^ (-(s * R / 8)) * (9 : ℝ) ^ d * (Real.exp (R ^ 2 * σ ^ 2 / 4) * 2) ^ 2) ^ j := by
  set E : ℝ := Real.exp (R ^ 2 * σ ^ 2 / 4) * 2 with hEdef
  set r0 : ℝ := (3 : ℝ) ^ (-(s * R / 8)) with hr0
  set A : ℝ := (9 : ℝ) ^ d with hA
  have hE1 : 1 ≤ E := by
    have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ R ^ 2 * σ ^ 2 / 4)
    rw [hEdef]; linarith
  have hA1 : 1 ≤ A := one_le_pow₀ (by norm_num)
  have hr00 : 0 ≤ r0 := by positivity
  have hdisc : ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) ^ R = r0 ^ j := by
    rw [hr0, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hcard : (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) ≤ A * A ^ j := by
    have hnat : (2 * 3 ^ (2 * j + 1) + 1) ^ d ≤ (9 ^ d) ^ (j + 1) := by
      have hb : 2 * 3 ^ (2 * j + 1) + 1 ≤ 9 ^ (j + 1) := by
        have h9 : 9 ^ (j + 1) = 3 * 3 ^ (2 * j + 1) := by
          rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring,
            pow_succ]
          ring
        rw [h9]
        have : 1 ≤ 3 ^ (2 * j + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      calc (2 * 3 ^ (2 * j + 1) + 1) ^ d ≤ (9 ^ (j + 1)) ^ d := Nat.pow_le_pow_left hb d
        _ = (9 ^ d) ^ (j + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
    have hcast : (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) ≤ (((9 ^ d) ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    refine hcast.trans (le_of_eq ?_)
    rw [hA]
    push_cast
    rw [pow_succ]
    ring
  have hpowE : E ^ (2 * j + 1) = E * (E ^ 2) ^ j := by
    rw [pow_succ, pow_mul]
    ring
  have hr0le : r0 ^ j ≤ (r0 * A * E ^ 2) ^ j := by
    refine pow_le_pow_left₀ hr00 ?_ j
    have : 1 ≤ A * E ^ 2 := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ hE1)
    nlinarith
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (R - 1) := by positivity
  unfold aux_prefix_praw_term
  rw [hdisc, ← hEdef]
  calc r0 ^ j * ((2 : ℝ) ^ (R - 1) *
        ((((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) * E ^ (2 * j + 1) + CB)) ≤
      r0 ^ j * ((2 : ℝ) ^ (R - 1) * (A * A ^ j * E ^ (2 * j + 1) + CB)) := by
        gcongr
    _ = (2 : ℝ) ^ (R - 1) * (A * E * (r0 * A * E ^ 2) ^ j + CB * r0 ^ j) := by
        rw [hpowE, mul_pow, mul_pow]
        ring_nf
    _ ≤ (2 : ℝ) ^ (R - 1) * (A * E * (r0 * A * E ^ 2) ^ j + CB * (r0 * A * E ^ 2) ^ j) := by
        gcongr
    _ = ((2 : ℝ) ^ (R - 1) * (A * E + CB)) * (r0 * A * E ^ 2) ^ j := by ring

/-- The `Psc` moment series is summable. -/
theorem aux_prefix_praw_term_summable (d : ℕ) (s R σ CB : ℝ) (hs : 0 < s) (hR : 1 ≤ R)
    (hRs : 32 * ((d : ℝ) + 1) ≤ s * R) (hσ : 16 * R * σ ^ 2 ≤ s) (hCB : 0 ≤ CB) :
    Summable (aux_prefix_praw_term d s R σ CB) := by
  have hρ := aux_prefix_praw_ratio_lt_one d s R σ hs hR hRs hσ
  have hρ0 : (0 : ℝ) ≤
      (3 : ℝ) ^ (-(s * R / 8)) * (9 : ℝ) ^ d * (Real.exp (R ^ 2 * σ ^ 2 / 4) * 2) ^ 2 := by
    positivity
  exact Summable.of_nonneg_of_le (aux_prefix_praw_term_nonneg d s R σ CB hCB)
    (aux_prefix_praw_term_le_geom d s R σ CB hCB)
    ((summable_geometric_of_lt_one hρ0 hρ).mul_left _)

end SubdiffusiveProcess.Paper
