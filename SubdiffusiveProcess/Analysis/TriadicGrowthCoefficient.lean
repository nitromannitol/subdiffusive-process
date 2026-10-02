import Mathlib
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess

theorem summable_triadicGrowthCoefficients
    {d : ℕ} (hd : 2 ≤ d) (r t : ℝ) (hr : 0 < r)
    (ht : (d : ℝ) - 1 < t) :
    Summable (fun n : ℕ => Real.sqrt
      ((((r / (3 : ℝ) ^ n) / 3) ^ t) *
        ((((r / (3 : ℝ) ^ n) / 3) ^ d) *
          ((r / (3 : ℝ) ^ n) ^ d))⁻¹ *
        (Real.sqrt (d : ℝ) * (r / (3 : ℝ) ^ n)) ^ ((d : ℝ) + 1))) := by
  set ε : ℝ := t - (d : ℝ) + 1 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  set ρ : ℝ := (3 : ℝ) ^ (-ε) with hρdef
  have hρnonneg : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hρlt1 : ρ < 1 := by
    rw [hρdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K : ℝ := (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) * r ^ ε with hKdef
  have hKnonneg : 0 ≤ K := by rw [hKdef]; positivity
  have hkey : ∀ n : ℕ,
      (((r / (3 : ℝ) ^ n) / 3) ^ t) *
        ((((r / (3 : ℝ) ^ n) / 3) ^ d) *
          ((r / (3 : ℝ) ^ n) ^ d))⁻¹ *
        (Real.sqrt (d : ℝ) * (r / (3 : ℝ) ^ n)) ^ ((d : ℝ) + 1)
      = K * ρ ^ n := by
    intro n
    have h3n_pos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    have hAn_pos : (0 : ℝ) < r / (3 : ℝ) ^ n := div_pos hr h3n_pos
    set A : ℝ := r / (3 : ℝ) ^ n with hAdef
    have hA_ne : A ≠ 0 := hAn_pos.ne'
    have hstep1 : ((A / 3) ^ d * A ^ d)⁻¹ = (3 : ℝ) ^ d / A ^ (2 * d) := by
      rw [div_pow, div_mul_eq_mul_div, ← pow_add, ← two_mul, inv_div]
    have hstep2 : (A / 3) ^ t = A ^ t * (3 : ℝ) ^ (-t) := by
      rw [div_eq_mul_inv, Real.mul_rpow hAn_pos.le (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹),
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    have hstep3 : (Real.sqrt (d : ℝ) * A) ^ ((d : ℝ) + 1)
        = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * A ^ ((d : ℝ) + 1) :=
      Real.mul_rpow (Real.sqrt_nonneg _) hAn_pos.le
    have hpow_combine : A ^ t * (A ^ (2 * d))⁻¹ * A ^ ((d : ℝ) + 1) = A ^ ε := by
      rw [← Real.rpow_natCast A (2 * d), ← Real.rpow_neg hAn_pos.le,
        ← Real.rpow_add hAn_pos, ← Real.rpow_add hAn_pos]
      congr 1
      push_cast
      rw [hεdef]
      ring
    have hAeps : A ^ ε = r ^ ε * ρ ^ n := by
      have hAform : A = r * (3 : ℝ) ^ (-(n : ℝ)) := by
        rw [hAdef, div_eq_mul_inv, ← Real.rpow_natCast (3 : ℝ) n,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      rw [hAform, Real.mul_rpow hr.le (Real.rpow_nonneg (by norm_num) _)]
      congr 1
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hρdef,
        ← Real.rpow_natCast ((3 : ℝ) ^ (-ε)) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    calc
      (A / 3) ^ t * ((A / 3) ^ d * A ^ d)⁻¹ * (Real.sqrt (d : ℝ) * A) ^ ((d : ℝ) + 1)
          = (A ^ t * (3 : ℝ) ^ (-t)) * ((3 : ℝ) ^ d / A ^ (2 * d)) *
              ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * A ^ ((d : ℝ) + 1)) := by
            rw [hstep1, hstep2, hstep3]
      _ = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * ((3 : ℝ) ^ (-t) * (3 : ℝ) ^ d) *
            (A ^ t * (A ^ (2 * d))⁻¹ * A ^ ((d : ℝ) + 1)) := by
            rw [div_eq_mul_inv]; ring
      _ = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) * A ^ ε := by
            rw [hpow_combine, ← Real.rpow_natCast (3 : ℝ) d,
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
              show (-t + (d : ℝ)) = (d : ℝ) - t from by ring]
      _ = K * ρ ^ n := by
            rw [hAeps, hKdef]
            ring
  have hsqrt_pow : ∀ n : ℕ, Real.sqrt (K * ρ ^ n) = Real.sqrt K * (Real.sqrt ρ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← mul_assoc,
          Real.sqrt_mul (mul_nonneg hKnonneg (pow_nonneg hρnonneg n)), ih, pow_succ]
        ring
  have hsqrtρ_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg _
  have hsqrtρ_lt1 : Real.sqrt ρ < 1 := by
    nlinarith [Real.sq_sqrt hρnonneg, Real.sqrt_nonneg ρ]
  have hgeom : Summable (fun n : ℕ => Real.sqrt K * (Real.sqrt ρ) ^ n) :=
    (summable_geometric_of_lt_one hsqrtρ_nonneg hsqrtρ_lt1).mul_left (Real.sqrt K)
  refine hgeom.congr (fun n => ?_)
  rw [← hsqrt_pow, hkey]

end SubdiffusiveProcess
