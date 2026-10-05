module

public import Mathlib

@[expose] public section

/-!
# Khintchine-type bound for a finite sign average

For `d : ι → ℝ` and `p > 0`, the average of `|∑ ε_i d_i|^p` over all sign vectors is at most
`2 e^{-p/2} p^{p/2} (∑ d_i²)^{p/2}`.  (Proof: `x^p ≤ (p/t)^p e^{-p} e^{t x}` and `E e^{t ∑ ε_i d_i} ≤ e^{t² ∑ d_i² / 2}`.)
-/

namespace SubdiffusiveProcess.Rosenthal

open Finset

/-- The sign attached to a Boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

theorem sgn_neg (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]

/-- The moment generating function of a random sign sum is sub-Gaussian (finite average, unnormalized). -/
theorem sum_exp_signs_le {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (t : ℝ) :
    ∑ s : ι → Bool, Real.exp (t * ∑ i, sgn (s i) * d i) ≤
      2 ^ Fintype.card ι * Real.exp (t ^ 2 * (∑ i, d i ^ 2) / 2) := by
  classical
  have h1 : ∀ s : ι → Bool, Real.exp (t * ∑ i, sgn (s i) * d i) =
      ∏ i, Real.exp (t * (sgn (s i) * d i)) := by
    intro s
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  have key : ∑ s : ι → Bool, ∏ i, Real.exp (t * (sgn (s i) * d i)) =
      ∏ i, ∑ b : Bool, Real.exp (t * (sgn b * d i)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [key]
  have h2 : ∀ i, ∑ b : Bool, Real.exp (t * (sgn b * d i)) ≤ 2 * Real.exp (t ^ 2 * d i ^ 2 / 2) := by
    intro i
    rw [Fintype.sum_bool]
    simp only [sgn, ite_true, Bool.false_eq_true, ite_false]
    have := Real.cosh_le_exp_half_sq (t * d i)
    rw [Real.cosh_eq] at this
    have e1 : t * (1 * d i) = t * d i := by ring
    have e2 : t * (-1 * d i) = -(t * d i) := by ring
    rw [e1, e2]
    have e3 : (t * d i) ^ 2 / 2 = t ^ 2 * d i ^ 2 / 2 := by ring
    rw [e3] at this
    linarith
  calc ∏ i, ∑ b : Bool, Real.exp (t * (sgn b * d i))
      ≤ ∏ i, (2 * Real.exp (t ^ 2 * d i ^ 2 / 2)) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun b _ => (Real.exp_pos _).le))
          (fun i _ => h2 i)
    _ = 2 ^ Fintype.card ι * Real.exp (t ^ 2 * (∑ i, d i ^ 2) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
        congr 2
        rw [Finset.mul_sum, Finset.sum_div]

/-- `x^p ≤ (p/t)^p e^{-p} e^{t x}` for `x ≥ 0`, `t > 0`, `p > 0`. -/
theorem rpow_le_rpow_mul_exp (p t x : ℝ) (hp : 0 < p) (ht : 0 < t) (hx : 0 ≤ x) :
    x ^ p ≤ (p / t) ^ p * Real.exp (-p) * Real.exp (t * x) := by
  have h1 : t * x / p ≤ Real.exp (t * x / p - 1) := by
    have := Real.add_one_le_exp (t * x / p - 1); linarith
  have h2 : (t * x / p) ^ p ≤ (Real.exp (t * x / p - 1)) ^ p :=
    Real.rpow_le_rpow (by positivity) h1 hp.le
  have h3 : (Real.exp (t * x / p - 1)) ^ p = Real.exp (t * x) * Real.exp (-p) := by
    rw [← Real.exp_mul, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have h4 : x = (p / t) * (t * x / p) := by field_simp
  calc x ^ p = ((p / t) * (t * x / p)) ^ p := by rw [← h4]
    _ = (p / t) ^ p * (t * x / p) ^ p := Real.mul_rpow (by positivity) (by positivity)
    _ ≤ (p / t) ^ p * (Real.exp (t * x) * Real.exp (-p)) := by
        gcongr
        exact h2.trans h3.le
    _ = (p / t) ^ p * Real.exp (-p) * Real.exp (t * x) := by ring

/-- **Khintchine, finite sign average.** -/
theorem sum_abs_signs_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) {p : ℝ} (hp : 0 < p) :
    ∑ s : ι → Bool, |∑ i, sgn (s i) * d i| ^ p ≤
      2 ^ Fintype.card ι * ((2 * Real.exp (-p / 2) * p ^ (p / 2)) * (∑ i, d i ^ 2) ^ (p / 2)) := by
  classical
  set A : ℝ := ∑ i, d i ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hAz : A = 0
  · have hd : ∀ i, d i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (d i))).mp hAz i (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have : ∀ s : ι → Bool, ∑ i, sgn (s i) * d i = 0 := by
      intro s; simp [hd]
    simp only [this, abs_zero, Real.zero_rpow hp.ne', Finset.sum_const_zero]
    positivity
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
  set t : ℝ := Real.sqrt p / Real.sqrt A with ht
  have htpos : 0 < t := by positivity
  have ht2 : t ^ 2 * A = p := by
    rw [ht, div_pow, Real.sq_sqrt hp.le, Real.sq_sqrt hA0]
    field_simp
  have hpt : p / t = Real.sqrt p * Real.sqrt A := by
    rw [ht]
    have : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have h2 : p = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt hp.le).symm
    field_simp
    nlinarith [Real.mul_self_sqrt hp.le]
  have hpt_pow : (p / t) ^ p = p ^ (p / 2) * A ^ (p / 2) := by
    rw [hpt, Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hp.le, ← Real.rpow_mul hA0]
    congr 2 <;> ring
  -- pointwise bound
  have hpt_le : ∀ s : ι → Bool, |∑ i, sgn (s i) * d i| ^ p ≤
      (p / t) ^ p * Real.exp (-p) * (Real.exp (t * ∑ i, sgn (s i) * d i) +
        Real.exp (-t * ∑ i, sgn (s i) * d i)) := by
    intro s
    set y : ℝ := ∑ i, sgn (s i) * d i
    have h1 := rpow_le_rpow_mul_exp p t |y| hp htpos (abs_nonneg _)
    have h2 : Real.exp (t * |y|) ≤ Real.exp (t * y) + Real.exp (-t * y) := by
      rcases abs_cases y with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; have := Real.exp_pos (-t * y); linarith
      · rw [h]
        have e : t * -y = -t * y := by ring
        rw [e]; have := Real.exp_pos (t * y); linarith
    calc |y| ^ p ≤ (p / t) ^ p * Real.exp (-p) * Real.exp (t * |y|) := h1
      _ ≤ (p / t) ^ p * Real.exp (-p) * (Real.exp (t * y) + Real.exp (-t * y)) := by gcongr
  calc ∑ s : ι → Bool, |∑ i, sgn (s i) * d i| ^ p
      ≤ ∑ s : ι → Bool, (p / t) ^ p * Real.exp (-p) * (Real.exp (t * ∑ i, sgn (s i) * d i) +
        Real.exp (-t * ∑ i, sgn (s i) * d i)) := Finset.sum_le_sum (fun s _ => hpt_le s)
    _ = (p / t) ^ p * Real.exp (-p) * (∑ s : ι → Bool, Real.exp (t * ∑ i, sgn (s i) * d i) +
        ∑ s : ι → Bool, Real.exp (-t * ∑ i, sgn (s i) * d i)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (p / t) ^ p * Real.exp (-p) * (2 ^ Fintype.card ι * Real.exp (t ^ 2 * A / 2) +
        2 ^ Fintype.card ι * Real.exp ((-t) ^ 2 * A / 2)) := by
        gcongr
        · exact sum_exp_signs_le d t
        · exact sum_exp_signs_le d (-t)
    _ = 2 ^ Fintype.card ι * ((2 * Real.exp (-p / 2) * p ^ (p / 2)) * A ^ (p / 2)) := by
        have e1 : (-t) ^ 2 * A / 2 = p / 2 := by rw [neg_sq, ht2]
        have e2 : t ^ 2 * A / 2 = p / 2 := by rw [ht2]
        rw [e1, e2, hpt_pow]
        have e3 : Real.exp (-p) * Real.exp (p / 2) = Real.exp (-p / 2) := by
          rw [← Real.exp_add]; congr 1; ring
        calc p ^ (p / 2) * A ^ (p / 2) * Real.exp (-p) *
              (2 ^ Fintype.card ι * Real.exp (p / 2) + 2 ^ Fintype.card ι * Real.exp (p / 2))
            = 2 ^ Fintype.card ι * (2 * (Real.exp (-p) * Real.exp (p / 2)) * p ^ (p / 2) * A ^ (p / 2)) := by
              ring
          _ = _ := by rw [e3]

end SubdiffusiveProcess.Rosenthal
