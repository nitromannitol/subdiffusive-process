module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open scoped BigOperators

noncomputable section

/-- The per-scale ratio left after the entropy factor is paired with one
exponential factor. -/
noncomputable def entropyRatio (d : ℕ) (rate : ℝ) : ℝ :=
  (3 : ℝ) ^ d * Real.exp (-rate)

theorem entropyRatio_nonneg (d : ℕ) (rate : ℝ) : 0 ≤ entropyRatio d rate :=
  mul_nonneg (by positivity) (Real.exp_pos _).le

/-- Under the printed smallness condition the ratio is at most `exp(-rate/2)`,
hence at most `1/2`. -/
theorem entropyRatio_le_exp_half {d : ℕ} {rate : ℝ}
    (hsmall : (d : ℝ) * Real.log 3 + Real.log 2 ≤ rate / 2) :
    entropyRatio d rate ≤ Real.exp (-(rate / 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (3 : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log 3) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  rw [entropyRatio, hpow, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith

theorem entropyRatio_le_half {d : ℕ} {rate : ℝ}
    (hsmall : (d : ℝ) * Real.log 3 + Real.log 2 ≤ rate / 2) :
    entropyRatio d rate ≤ 1 / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg (by norm_num))
  have hpow : (3 : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log 3) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hhalf : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [entropyRatio, hpow, ← Real.exp_add, ← hhalf]
  refine Real.exp_le_exp.2 ?_
  linarith

/-- A partial geometric sum with ratio at most `1/2` is at most `2`. -/
theorem geom_partial_sum_le_two {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho ≤ 1 / 2)
    (N : ℕ) : ∑ j ∈ Finset.range N, rho ^ j ≤ 2 := by
  have hlt : rho < 1 := lt_of_le_of_lt h1 (by norm_num)
  have hsummable : Summable (fun j : ℕ => rho ^ j) :=
    summable_geometric_of_lt_one h0 hlt
  have hsum := hsummable.sum_le_tsum (Finset.range N)
    (fun j (_ : j ∉ Finset.range N) => pow_nonneg h0 j)
  rw [tsum_geometric_of_lt_one h0 hlt] at hsum
  refine hsum.trans ?_
  have h1r : (1 : ℝ) / 2 ≤ 1 - rho := by linarith
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) h1r
  simpa [one_div] using hinv

/-- Reflecting the summation index turns the descending powers
`rho ^ (m - n)`, `n ≤ m - q`, into the ascending powers `rho ^ (q + j)`. -/
theorem sum_pow_sub_eq_pow_mul {rho : ℝ} {q m : ℕ} (hqm : q ≤ m) :
    ∑ n ∈ Finset.range (m - q + 1), rho ^ (m - n) =
      rho ^ q * ∑ j ∈ Finset.range (m - q + 1), rho ^ j := by
  rw [Finset.mul_sum]
  rw [← Finset.sum_range_reflect (fun n => rho ^ (m - n)) (m - q + 1)]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjlt : j < m - q + 1 := Finset.mem_range.1 hj
  have hidx : m - (m - q + 1 - 1 - j) = q + j := by omega
  rw [hidx, pow_add]

/-- **The entropy absorption step.**  The union-bound sum over inner scales
collapses to a geometric tail in the depth `q`. -/
theorem sum_entropy_exp_le {d q m : ℕ} {rate : ℝ}
    (hqm : q ≤ m) (hrate : 0 < rate)
    (hsmall : (d : ℝ) * Real.log 3 + Real.log 2 ≤ rate / 2) :
    ∑ n ∈ Finset.range (m - q + 1),
        ((3 ^ (d * (m - n)) : ℕ) : ℝ) *
          Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1)) ≤
      2 * Real.exp (-(rate / 2 * (q : ℝ))) := by
  set rho : ℝ := entropyRatio d rate with hrhodef
  have hrho0 : 0 ≤ rho := entropyRatio_nonneg d rate
  have hrhohalf : rho ≤ 1 / 2 := entropyRatio_le_half hsmall
  have hrhoexp : rho ≤ Real.exp (-(rate / 2)) := entropyRatio_le_exp_half hsmall
  -- rewrite each term exactly as `exp (-rate) * rho ^ (m - n)`
  have hterm : ∀ n ∈ Finset.range (m - q + 1),
      ((3 ^ (d * (m - n)) : ℕ) : ℝ) *
          Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1)) =
        Real.exp (-rate) * rho ^ (m - n) := by
    intro n hn
    have hnle : n ≤ m := by
      have := Finset.mem_range.1 hn
      omega
    have hcast : ((m : ℝ) - (n : ℝ)) = ((m - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hnle]
    have hnum : ((3 ^ (d * (m - n)) : ℕ) : ℝ) = ((3 : ℝ) ^ d) ^ (m - n) := by
      push_cast
      rw [pow_mul]
    have hexp : Real.exp (-rate * (((m - n : ℕ) : ℝ) + 1)) =
        Real.exp (-rate) * (Real.exp (-rate)) ^ (m - n) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [hcast, hnum, hexp, hrhodef, entropyRatio, mul_pow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_pow_sub_eq_pow_mul (rho := rho) hqm]
  -- the geometric factor
  have hgeom : ∑ j ∈ Finset.range (m - q + 1), rho ^ j ≤ 2 :=
    geom_partial_sum_le_two hrho0 hrhohalf _
  have hpowq : rho ^ q ≤ Real.exp (-(rate / 2 * (q : ℝ))) := by
    calc rho ^ q ≤ (Real.exp (-(rate / 2))) ^ q :=
          pow_le_pow_left₀ hrho0 hrhoexp q
      _ = Real.exp (-(rate / 2 * (q : ℝ))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hexp1 : Real.exp (-rate) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  have hpow_nonneg : (0 : ℝ) ≤ rho ^ q := pow_nonneg hrho0 q
  have hexp_pos : (0 : ℝ) < Real.exp (-rate) := Real.exp_pos _
  calc Real.exp (-rate) *
        (rho ^ q * ∑ j ∈ Finset.range (m - q + 1), rho ^ j)
      ≤ 1 * (rho ^ q * 2) := by
        have hsum_nonneg : (0 : ℝ) ≤ ∑ j ∈ Finset.range (m - q + 1), rho ^ j :=
          Finset.sum_nonneg fun j _ => pow_nonneg hrho0 j
        refine mul_le_mul hexp1 ?_ (mul_nonneg hpow_nonneg hsum_nonneg)
          (by norm_num)
        exact mul_le_mul_of_nonneg_left hgeom hpow_nonneg
    _ = 2 * rho ^ q := by ring
    _ ≤ 2 * Real.exp (-(rate / 2 * (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hpowq (by norm_num)

/-- The shifted form of `sum_entropy_exp_le`, matching the landed
error-stopping tails whose exponent carries `(q - 1)_+` rather than `q`. -/
theorem sum_entropy_exp_le_shift {d q m : ℕ} {rate : ℝ}
    (hqm : q ≤ m) (hrate : 0 < rate)
    (hsmall : (d : ℝ) * Real.log 3 + Real.log 2 ≤ rate / 2) :
    ∑ n ∈ Finset.range (m - q + 1),
        ((3 ^ (d * (m - n)) : ℕ) : ℝ) *
          Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1)) ≤
      2 * Real.exp (-(rate / 2 * max ((q : ℝ) - 1) 0)) := by
  refine (sum_entropy_exp_le hqm hrate hsmall).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  have hmax : max ((q : ℝ) - 1) 0 ≤ (q : ℝ) :=
    max_le (by linarith) (Nat.cast_nonneg q)
  nlinarith [hrate.le]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
