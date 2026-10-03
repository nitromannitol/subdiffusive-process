module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Transferring an affine quadratic saving

Lemma 74, (E096), for actual nonnegative real quadratic forms. The proof
uses weighted quadratic inequalities instead of introducing square roots
of seminorms. No analytic or ABK input is used.
-/

namespace SubdiffusiveProcess

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A weighted triangle inequality for a nonnegative quadratic form. -/
theorem quadratic_add_le (Q : QuadraticForm ℝ V) (hQ : ∀ v, 0 ≤ Q v)
    (x y : V) {t : ℝ} (ht : 0 < t) :
    Q (x + y) ≤ (1 + 1 / t) * Q x + (1 + t) * Q y := by
  have h := hQ (x - t • y)
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, Q.map_neg, Q.map_smul,
    QuadraticMap.polar_neg_right, Q.polar_smul_right] at h
  simp only [smul_eq_mul] at h
  rw [QuadraticMap.map_add Q]
  apply (mul_le_mul_iff_left₀ ht).mp
  have heq : ((1 + 1 / t) * Q x + (1 + t) * Q y) * t =
      (t + 1) * Q x + (t + t * t) * Q y := by
    field_simp
  rw [heq]
  nlinarith

/-- The saving estimate (E096), with the constants of the dossier. -/
theorem quadratic_form_saving_of_nonneg_gap (Q B : QuadraticForm ℝ V)
    (hQ : ∀ v, 0 ≤ Q v) (hB : ∀ v, 0 ≤ B v)
    {gap a : ℝ} (hgap : 0 ≤ gap) (ha : 0 < a) (ha₁ : a ≤ 1)
    (hdom : ∀ v, B v ≤ gap * Q v) (b l : V)
    (hsaving : a * gap * Q l ≤ B l) :
    gap * (a / 2 * Q b - 4 * Q (b - l)) ≤ B b := by
  have hq := quadratic_add_le Q hQ l (b - l) (t := 3) (by norm_num)
  have hb := quadratic_add_le B hB b (-(b - l)) (t := 2) (by norm_num)
  have hsum : l + (b - l) = b := by abel
  have hsub : b + -(b - l) = l := by abel
  rw [hsum] at hq
  rw [hsub, B.map_neg] at hb
  norm_num at hq hb
  have hq' := mul_le_mul_of_nonneg_left hq (mul_nonneg (le_of_lt ha) hgap)
  have herror := mul_le_mul_of_nonneg_right ha₁ (mul_nonneg hgap (hQ (b - l)))
  have hdom' := hdom (b - l)
  nlinarith

/-- Lemma 74 for an arbitrary real gap. If it is negative, domination and
nonnegativity force both quadratic forms to vanish, so no extra gap
hypothesis is needed in the standalone statement. -/
theorem quadratic_form_saving (Q B : QuadraticForm ℝ V)
    (hQ : ∀ v, 0 ≤ Q v) (hB : ∀ v, 0 ≤ B v)
    {gap a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    (hdom : ∀ v, B v ≤ gap * Q v) (b l : V)
    (hsaving : a * gap * Q l ≤ B l) :
    gap * (a / 2 * Q b - 4 * Q (b - l)) ≤ B b := by
  by_cases hgap : 0 ≤ gap
  · exact quadratic_form_saving_of_nonneg_gap Q B hQ hB hgap ha ha₁ hdom b l hsaving
  · have hzero : ∀ v, Q v = 0 := by
      intro v
      have hg : gap < 0 := lt_of_not_ge hgap
      have hprod : 0 ≤ gap * Q v := le_trans (hB v) (hdom v)
      rcases eq_or_lt_of_le (hQ v) with hz | hp
      · exact hz.symm
      · have hneg := mul_neg_of_neg_of_pos hg hp
        linarith
    rw [hzero b, hzero (b - l)]
    simpa only [mul_zero, sub_zero] using hB b

end SubdiffusiveProcess
