module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- Deterministic final step from finite bank comparisons and a common
factor-times-limit envelope to the two coarse matrix bounds. -/
theorem lem_as_coarse_shallow_grid_retained_bank_algebra (d : ℕ)
    (s osc C K B S : ℝ) (hSpos : 0 < s) (hC : 0 ≤ C)
    (FD FN ZD ZN : Fin d → ℝ)
    (hZD : ∀ i, 0 ≤ ZD i) (hZN : ∀ i, 0 ≤ ZN i)
    (hFD : ∀ i, FD i ≤ C * (1 + ZD i))
    (hFN : ∀ i, FN i ≤ C * (1 + ZN i))
    (hEnvD : ∀ i, |Real.exp osc * (s + s⁻¹) * (1 + ZD i)| ≤ K)
    (hEnvN : ∀ i, |Real.exp osc * (s + s⁻¹) * (1 + ZN i)| ≤ K)
    (hB : B ≤ (s * Real.exp osc) * ∑ i, FD i)
    (hS : S ≤ (s * Real.exp (-osc))⁻¹ * ∑ i, FN i) :
    B + S ≤ 2 * (d : ℝ) * C * K := by
  have hsInv : 0 < s⁻¹ := inv_pos.mpr hSpos
  have hsSum : 0 ≤ s + s⁻¹ := by linarith
  have hfactorD : ∀ i, 0 ≤ 1 + ZD i := by intro i; linarith [hZD i]
  have hfactorN : ∀ i, 0 ≤ 1 + ZN i := by intro i; linarith [hZN i]
  have hpairD (i : Fin d) : s * Real.exp osc * (1 + ZD i) ≤ K := by
    have hpair : 0 ≤ Real.exp osc * (s + s⁻¹) * (1 + ZD i) := by
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hsSum) (hfactorD i)
    have henv : Real.exp osc * (s + s⁻¹) * (1 + ZD i) ≤ K := by
      simpa [abs_of_nonneg hpair] using hEnvD i
    have hle : s * Real.exp osc ≤ Real.exp osc * (s + s⁻¹) := by
      nlinarith [mul_nonneg (Real.exp_pos osc).le hsInv.le]
    exact (mul_le_mul_of_nonneg_right hle (hfactorD i)).trans henv
  have hpairN (i : Fin d) : (s * Real.exp (-osc))⁻¹ * (1 + ZN i) ≤ K := by
    have hpair : 0 ≤ Real.exp osc * (s + s⁻¹) * (1 + ZN i) := by
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hsSum) (hfactorN i)
    have henv : Real.exp osc * (s + s⁻¹) * (1 + ZN i) ≤ K := by
      simpa [abs_of_nonneg hpair] using hEnvN i
    have hinv : (s * Real.exp (-osc))⁻¹ = Real.exp osc * s⁻¹ := by
      rw [mul_inv_rev, ← Real.exp_neg]
      ring_nf
    rw [hinv]
    have hle : Real.exp osc * s⁻¹ ≤ Real.exp osc * (s + s⁻¹) := by
      nlinarith [mul_nonneg (Real.exp_pos osc).le hSpos.le]
    exact (mul_le_mul_of_nonneg_right hle (hfactorN i)).trans henv
  have hBsum : B ≤ (d : ℝ) * C * K := by
    calc
      B ≤ (s * Real.exp osc) * ∑ i, FD i := hB
      _ = ∑ i : Fin d, (s * Real.exp osc) * FD i := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin d, C * K := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          (s * Real.exp osc) * FD i ≤
              (s * Real.exp osc) * (C * (1 + ZD i)) :=
            mul_le_mul_of_nonneg_left (hFD i) (mul_nonneg hSpos.le (Real.exp_pos _).le)
          _ = C * (s * Real.exp osc * (1 + ZD i)) := by ring
          _ ≤ C * K := mul_le_mul_of_nonneg_left (hpairD i) hC
      _ = (d : ℝ) * C * K := by simp; ring
  have hSsum : S ≤ (d : ℝ) * C * K := by
    calc
      S ≤ (s * Real.exp (-osc))⁻¹ * ∑ i, FN i := hS
      _ = ∑ i : Fin d, (s * Real.exp (-osc))⁻¹ * FN i := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin d, C * K := by
        apply Finset.sum_le_sum
        intro i hi
        have hmult : 0 ≤ (s * Real.exp (-osc))⁻¹ := by positivity
        calc
          (s * Real.exp (-osc))⁻¹ * FN i ≤
              (s * Real.exp (-osc))⁻¹ * (C * (1 + ZN i)) :=
            mul_le_mul_of_nonneg_left (hFN i) hmult
          _ = C * ((s * Real.exp (-osc))⁻¹ * (1 + ZN i)) := by ring
          _ ≤ C * K := mul_le_mul_of_nonneg_left (hpairN i) hC
      _ = (d : ℝ) * C * K := by simp; ring
  linarith [hBsum, hSsum]

end SubdiffusiveProcess.Paper

