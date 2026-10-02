import Mathlib
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeightedEnergyComparison
import Homogenization.Probability.IndependentSums.GammaSigma.Basic

/-! Elementary exponential differences and Gaussian absorption.
The first inequality adapts `SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments`.
The power bound reuses the author's CoarseGraining Gaussian-moment calculus. -/
noncomputable section
namespace SubdiffusiveProcess.Probability

lemma abs_exp_sub_one_le (u : ℝ) :
    |Real.exp u - 1| ≤ |u| * Real.exp |u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hu))]
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
    rw [Real.exp_neg, mul_add, mul_one, mul_inv_cancel₀ (Real.exp_ne_zero u)] at h
    nlinarith
  · rw [abs_of_neg hu, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hu.le))]
    have hlin := Real.add_one_le_exp u
    have hexp : 1 ≤ Real.exp (-u) := Real.one_le_exp (neg_nonneg.mpr hu.le)
    nlinarith [mul_le_mul_of_nonneg_left hexp (neg_nonneg.mpr hu.le)]

lemma abs_exp_sub_one_add_le (u : ℝ) :
    |Real.exp u - (1 + u)| ≤ 3 * u ^ (2 : ℕ) * Real.exp |u| := by
  have h := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.abs_exp_sub_one_sub_id_le_half_sq_mul_exp_abs u
  have hid : Real.exp u - (1 + u) = Real.exp u - 1 - u := by ring
  rw [hid]
  calc
    _ ≤ (u ^ (2 : ℕ) / 2) * Real.exp |u| := h
    _ ≤ 3 * u ^ (2 : ℕ) * Real.exp |u| :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg u]) (Real.exp_pos _).le

lemma rpow_le_gaussian {y m : ℝ} (hy : 0 ≤ y) (hm : 0 < m) :
    y ^ m ≤ (m ^ (1 / 2 : ℝ)) ^ m * Real.exp (y ^ (2 : ℕ) / 2) := by
  rcases eq_or_lt_of_le hy with rfl | hypos
  · rw [Real.zero_rpow hm.ne']
    positivity
  have h := Homogenization.IndependentSums.rpow_mul_exp_neg_half_le
    (r := m / 2) (u := y ^ (2 : ℕ)) (by positivity) (by positivity)
  have hp : (y ^ (2 : ℕ)) ^ (m / 2) = y ^ m := by
    rw [← Real.rpow_two, ← Real.rpow_mul hy]
    congr 1
    ring
  have hc : ((2 * (m / 2)) / Real.exp 1) ^ (m / 2) ≤ m ^ (m / 2) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [div_le_iff₀ (Real.exp_pos _)]
    have he := mul_le_mul_of_nonneg_left (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) hm.le
    nlinarith
  rw [hp] at h
  have hmul := mul_le_mul_of_nonneg_right (h.trans hc) (Real.exp_pos (y ^ (2 : ℕ) / 2)).le
  have heq : Real.exp (-y ^ (2 : ℕ) / 2) * Real.exp (y ^ (2 : ℕ) / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show -y ^ (2 : ℕ) / 2 + y ^ (2 : ℕ) / 2 = 0 by ring, Real.exp_zero]
  simpa only [mul_assoc, heq, mul_one, ← Real.rpow_mul hm.le,
    one_div, inv_mul_eq_div] using hmul

lemma rpow_mul_exp_linear_le {y m a : ℝ} (hy : 0 ≤ y) (hm : 0 < m) :
    y ^ m * Real.exp (a * y) ≤
      (m ^ (1 / 2 : ℝ)) ^ m * Real.exp (y ^ (2 : ℕ) + a ^ (2 : ℕ) / 2) := by
  have he : a * y ≤ y ^ (2 : ℕ) / 2 + a ^ (2 : ℕ) / 2 := by
    nlinarith [sq_nonneg (y - a)]
  calc
    _ ≤ ((m ^ (1 / 2 : ℝ)) ^ m * Real.exp (y ^ (2 : ℕ) / 2)) *
        Real.exp (y ^ (2 : ℕ) / 2 + a ^ (2 : ℕ) / 2) :=
      mul_le_mul (rpow_le_gaussian hy hm) (Real.exp_le_exp.mpr he)
        (Real.exp_pos _).le
        (mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hm.le _) _) (Real.exp_pos _).le)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end SubdiffusiveProcess.Probability
