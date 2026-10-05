module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Two nonnegative score budgets bound the number of scales rejected by a
fixed error cap. This is finite arithmetic and makes no stochastic assertion.
-/
open scoped BigOperators
namespace SubdiffusiveProcess

/-- The failure indicator is paid by the bad score plus the rescaled error score. -/
theorem bad_score_indicator_le {z e tau : ℝ} (hz : 0 ≤ z) (he : 0 ≤ e) (htau : 0 < tau) :
    (if z < 1 ∧ e ≤ tau then (0 : ℝ) else 1) ≤ z + tau⁻¹ * e := by
  split_ifs with h
  · positivity
  · by_cases hZ : z < 1
    · have hE : tau ≤ e := le_of_lt (lt_of_not_ge (fun hh => h ⟨hZ, hh⟩))
      have hmul := mul_le_mul_of_nonneg_left hE (inv_pos.mpr htau).le
      rw [inv_mul_cancel₀ htau.ne'] at hmul
      linarith only [hmul, hz]
    · have hh : 1 ≤ z := le_of_not_gt hZ
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg (inv_pos.mpr htau).le he))

/-- A two-score prefix controls the number of scales where either test fails. -/
theorem bad_score_card_le {ι : Type*} (S : Finset ι) (Z E : ι → ℝ)
    (tau : ℝ) (htau : 0 < tau) (hZ : ∀ i ∈ S, 0 ≤ Z i) (hE : ∀ i ∈ S, 0 ≤ E i) :
    ((@Finset.filter ι (fun i => ¬ (Z i < 1 ∧ E i ≤ tau)) (Classical.decPred _) S).card : ℝ) ≤
      (∑ i ∈ S, Z i) + tau⁻¹ * ∑ i ∈ S, E i := by
  classical
  have h := Finset.sum_le_sum (fun i hi => bad_score_indicator_le (hZ i hi) (hE i hi) htau)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  convert h using 1
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hg : Z i < 1 ∧ E i ≤ tau
  · rw [ite_eq_right (not_not.mpr hg), ite_eq_left hg]
  · rw [ite_eq_left hg, ite_eq_right hg]

/-- Smaller prefix thresholds pay both the iteration score and its enlarged bad set. -/
theorem score_budget_rescale {ι : Type*} (S : Finset ι) (Z E : ι → ℝ)
    (tau lam len : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hlam : 0 ≤ lam) (hlen : 0 ≤ len)
    (hZ : ∀ i ∈ S, 0 ≤ Z i) (hE : ∀ i ∈ S, 0 ≤ E i)
    (hz : ∑ i ∈ S, Z i ≤ (lam * tau / 2) * len)
    (he : ∑ i ∈ S, E i ≤ (lam * tau / 2) * len) :
    (∑ i ∈ S, E i ≤ lam * len) ∧
    ((@Finset.filter ι (fun i => ¬ (Z i < 1 ∧ E i ≤ tau)) (Classical.decPred _) S).card : ℝ) <
      1 + lam * len := by
  have hbudget : lam * tau / 2 * len ≤ lam * len := by
    have hh := mul_le_mul_of_nonneg_left htau1 (mul_nonneg hlam hlen)
    nlinarith only [hh, mul_nonneg hlam hlen]
  refine ⟨he.trans hbudget, ?_⟩
  have hb := (bad_score_card_le S Z E tau htau hZ hE).trans
    (add_le_add hz (mul_le_mul_of_nonneg_left he (inv_pos.mpr htau).le))
  refine hb.trans_lt ?_
  have hcancel : tau⁻¹ * (lam * tau / 2 * len) = lam * len / 2 := by
      calc _ = (tau⁻¹ * tau) * (lam * len / 2) := by ring
        _ = _ := by rw [inv_mul_cancel₀ htau.ne', one_mul]
  rw [hcancel]
  have hh := mul_le_mul_of_nonneg_left htau1 (mul_nonneg hlam hlen)
  nlinarith only [hh]

end SubdiffusiveProcess
