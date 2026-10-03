module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Homogenization
open scoped BigOperators

noncomputable section

/-! ## Elementary square-root comparisons -/

/-- `√t ≤ t` above `1`. -/
theorem sqrt_le_self_of_one_le {t : ℝ} (ht : 1 ≤ t) : Real.sqrt t ≤ t := by
  have h0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt h0
  have hone : (1 : ℝ) ≤ Real.sqrt t := by
    have := Real.sqrt_le_sqrt ht
    simpa using this
  nlinarith

/-- Subadditivity of the square root. -/
theorem sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hkey : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = Real.sqrt a + Real.sqrt b :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))

/-- `1 ≤ √(n+1)`. -/
theorem one_le_natSucc_cast (n : ℕ) : (1 : ℝ) ≤ (n : ℝ) + 1 := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem one_le_sqrt_natSucc (n : ℕ) : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := by
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (one_le_natSucc_cast n)

/-- The split of the graded price of the derivative Borel–Cantelli:
`√(n+k+1) ≤ √(n+1) √(k+1)`. -/
theorem sqrt_natAdd_le_mul (n k : ℕ) :
    Real.sqrt ((n : ℝ) + (k : ℝ) + 1) ≤
      Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  nlinarith

/-! ## The geometric-times-square-root series -/

/-- `∑ q^k √(k+1)` converges for `0 ≤ q < 1`. -/
theorem summable_geom_mul_sqrt {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun k : ℕ => q ^ k * Real.sqrt ((k : ℝ) + 1) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have h1 : Summable fun k : ℕ => (k : ℝ) ^ 1 * q ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h2 : Summable fun k : ℕ => q ^ k := summable_geometric_of_lt_one hq0 hq1
  have hsum : Summable fun k : ℕ => q ^ k * ((k : ℝ) + 1) := by
    refine (h1.add h2).congr ?_
    intro k
    ring
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsum
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact sqrt_le_self_of_one_le (one_le_natSucc_cast k)

/-- The constant of the geometric derivative series. -/
def geomSqrtConst (q : ℝ) : ℝ := ∑' k : ℕ, q ^ k * Real.sqrt ((k : ℝ) + 1)

theorem geomSqrtConst_nonneg {q : ℝ} (hq0 : 0 ≤ q) : 0 ≤ geomSqrtConst q :=
  tsum_nonneg fun k => by positivity

/-- **The geometric derivative series.**  For every finite set of scales,
`∑ q^k √(n+k+1) ≤ C_q √(n+1)` with a constant independent of `n`. -/
theorem sum_geom_sqrt_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ)
    (s : Finset ℕ) :
    ∑ k ∈ s, q ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) ≤
      geomSqrtConst q * Real.sqrt ((n : ℝ) + 1) := by
  have hsummable := summable_geom_mul_sqrt hq0 hq1
  have hstep : ∀ k ∈ s, q ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) ≤
      Real.sqrt ((n : ℝ) + 1) * (q ^ k * Real.sqrt ((k : ℝ) + 1)) := by
    intro k _
    have := mul_le_mul_of_nonneg_left (sqrt_natAdd_le_mul n k)
      (pow_nonneg hq0 k)
    calc q ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)
        ≤ q ^ k * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) := this
      _ = Real.sqrt ((n : ℝ) + 1) * (q ^ k * Real.sqrt ((k : ℝ) + 1)) := by ring
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  rw [mul_comm (geomSqrtConst q)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  exact hsummable.sum_le_tsum s (fun k _ => by positivity)

/-! ## The high-scale comparison -/

/-- For `k ≥ n+2` the growing radius `2^{n+1}` is absorbed by the geometric
factor: `2^{n+1} 3^{-k} ≤ ½ (2/3)^k`.  This is what makes the printed tail
estimate a single `n`-independent geometric series. -/
theorem growingRadius_mul_inv_pow_le {n k : ℕ} (hk : n + 2 ≤ k) :
    (2 : ℝ) ^ (n + 1) * (((3 : ℝ) ^ k)⁻¹) ≤ (1 / 2) * (2 / 3 : ℝ) ^ k := by
  have h2 : (2 : ℝ) ^ (n + 2) ≤ (2 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hk
  have hexp : (2 : ℝ) ^ (n + 2) = 2 * (2 : ℝ) ^ (n + 1) := by ring
  have key : (2 : ℝ) ^ (n + 1) ≤ (1 / 2) * (2 : ℝ) ^ k := by
    rw [hexp] at h2
    linarith
  have hinv : (0 : ℝ) ≤ (((3 : ℝ) ^ k)⁻¹) := by positivity
  calc (2 : ℝ) ^ (n + 1) * (((3 : ℝ) ^ k)⁻¹)
      ≤ ((1 / 2) * (2 : ℝ) ^ k) * (((3 : ℝ) ^ k)⁻¹) :=
        mul_le_mul_of_nonneg_right key hinv
    _ = (1 / 2) * (2 / 3 : ℝ) ^ k := by
        rw [div_pow, div_eq_mul_inv]
        ring

/-! ## The dyadic index and the frozen `√(log(2+‖x‖))` form -/

variable {d : ℕ}

/-- The dyadic scale of a point: the least `n` with `2 + ‖x‖ ≤ 2ⁿ`. -/
def dyadicIndex (x : Vec d) : ℕ := ⌈Real.logb 2 (2 + ‖x‖)⌉₊

theorem one_le_two_add_norm (x : Vec d) : (1 : ℝ) ≤ 2 + ‖x‖ := by
  have := norm_nonneg x
  linarith

theorem logb_two_add_norm_nonneg (x : Vec d) :
    0 ≤ Real.logb 2 (2 + ‖x‖) :=
  Real.logb_nonneg (by norm_num) (one_le_two_add_norm x)

/-- The defining property of the dyadic index. -/
theorem two_add_norm_le_two_pow_dyadicIndex (x : Vec d) :
    2 + ‖x‖ ≤ (2 : ℝ) ^ (dyadicIndex x) := by
  have hpos : (0 : ℝ) < 2 + ‖x‖ := lt_of_lt_of_le zero_lt_one (one_le_two_add_norm x)
  have hle : Real.logb 2 (2 + ‖x‖) ≤ (dyadicIndex x : ℝ) := Nat.le_ceil _
  have h : (2 : ℝ) ^ (Real.logb 2 (2 + ‖x‖)) ≤ (2 : ℝ) ^ ((dyadicIndex x : ℕ) : ℝ) :=
    Real.rpow_le_rpow_left_iff (by norm_num) |>.2 hle
  rwa [Real.rpow_logb (by norm_num) (by norm_num) hpos, Real.rpow_natCast] at h

/-- The dyadic index is at most logarithmic. -/
theorem dyadicIndex_succ_le (x : Vec d) :
    (dyadicIndex x : ℝ) + 1 ≤ Real.log (2 + ‖x‖) / Real.log 2 + 2 := by
  have h := Nat.ceil_lt_add_one (logb_two_add_norm_nonneg x)
  simp only [Real.logb] at h
  have h' : (dyadicIndex x : ℝ) < Real.log (2 + ‖x‖) / Real.log 2 + 1 := h
  linarith

/-- The dimensional constant of the `√`-comparison. -/
def sqrtLogConst : ℝ := 1 / Real.sqrt (Real.log 2) + Real.sqrt 2

theorem sqrtLogConst_nonneg : (0 : ℝ) ≤ sqrtLogConst := by
  have h1 : (0 : ℝ) ≤ 1 / Real.sqrt (Real.log 2) := by positivity
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  rw [sqrtLogConst]
  linarith

/-- **The frozen `√(log(2+‖x‖))` form of the dyadic price.** -/
theorem sqrt_dyadicIndex_succ_le (x : Vec d) :
    Real.sqrt ((dyadicIndex x : ℝ) + 1) ≤
      sqrtLogConst * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (0 : ℝ) ≤ Real.log (2 + ‖x‖) :=
    Real.log_nonneg (one_le_two_add_norm x)
  have hdiv : (0 : ℝ) ≤ Real.log (2 + ‖x‖) / Real.log 2 :=
    div_nonneg hL hlog2.le
  have hstep : Real.sqrt ((dyadicIndex x : ℝ) + 1) ≤
      Real.sqrt (Real.log (2 + ‖x‖) / Real.log 2 + 2) :=
    Real.sqrt_le_sqrt (dyadicIndex_succ_le x)
  have hsplit : Real.sqrt (Real.log (2 + ‖x‖) / Real.log 2 + 2) ≤
      Real.sqrt (Real.log (2 + ‖x‖) / Real.log 2) + Real.sqrt 2 :=
    sqrt_add_le hdiv (by norm_num)
  have hquot : Real.sqrt (Real.log (2 + ‖x‖) / Real.log 2) =
      1 / Real.sqrt (Real.log 2) * Real.sqrt (Real.log (2 + ‖x‖)) := by
    rw [Real.sqrt_div hL]
    field_simp
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log (2 + ‖x‖)) := Real.sqrt_nonneg _
  have ha : (0 : ℝ) ≤ 1 / Real.sqrt (Real.log 2) := by positivity
  have hb : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hfinal : 1 / Real.sqrt (Real.log 2) * Real.sqrt (Real.log (2 + ‖x‖)) +
      Real.sqrt 2 ≤ sqrtLogConst * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
    rw [sqrtLogConst]
    nlinarith
  calc Real.sqrt ((dyadicIndex x : ℝ) + 1)
      ≤ Real.sqrt (Real.log (2 + ‖x‖) / Real.log 2 + 2) := hstep
    _ ≤ Real.sqrt (Real.log (2 + ‖x‖) / Real.log 2) + Real.sqrt 2 := hsplit
    _ = 1 / Real.sqrt (Real.log 2) * Real.sqrt (Real.log (2 + ‖x‖)) +
          Real.sqrt 2 := by rw [hquot]
    _ ≤ sqrtLogConst * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
