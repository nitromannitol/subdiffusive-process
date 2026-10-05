module

public import Mathlib.Tactic

@[expose] public section

/-! Positive numerical budgets for the upper and lower ranges of excess iteration.
No one-step PDE or probabilistic estimate is asserted. -/

noncomputable section
namespace SubdiffusiveProcess

/-- Finite maxima provide simultaneous upper and lower iteration budget constants. -/
theorem exists_iterationBudgetConstants (d : ℕ) (alpha Ceps Cdel E0 Cg : ℝ)
    (hE0 : 0 < E0) (hCg : 0 < Cg) :
    ∃ C2 C3 : ℝ, 0 ≤ C2 ∧ 0 ≤ C3 ∧
      11 + (E0 / (2 * Cg))⁻¹ ≤ C2 ∧ 2 * Ceps * Cg ≤ C2 ∧
      3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2 ∧ ((d : ℝ) + 3) / Real.log 3 ≤ C2 ∧
      9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2 ≤ C3 ∧
      Ceps * 5 * (9 * (d : ℝ) / 2) ≤ C3 ∧
      9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C3 ∧ (2 * (d : ℝ) + 4) / Real.log 3 ≤ C3 := by
  let C2 := max (max (11 + (E0 / (2 * Cg))⁻¹) (2 * Ceps * Cg))
    (max (3 * Cdel / (1 - (3 : ℝ) ^ (-alpha))) (((d : ℝ) + 3) / Real.log 3))
  let C3 := max (max (9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2) (Ceps * 5 * (9 * (d : ℝ) / 2)))
    (max (9 * Cdel / (1 - (3 : ℝ) ^ (-alpha))) ((2 * (d : ℝ) + 4) / Real.log 3))
  have hC2a : 11 + (E0 / (2 * Cg))⁻¹ ≤ C2 := (le_max_left _ _).trans (le_max_left _ _)
  have hC3a : 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2 ≤ C3 :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hc : 0 < min 1 (E0 / 5) := lt_min one_pos (by positivity)
  refine ⟨C2, C3, (by positivity : (0 : ℝ) ≤ 11 + (E0 / (2 * Cg))⁻¹).trans hC2a,
    (by positivity : (0 : ℝ) ≤ 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2).trans hC3a,
    hC2a, (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _),
    hC3a, (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩

/-- Choosing both small parameters below the error cap leaves half the budget for the cutoff score. -/
theorem iteration_error_cap (Cg E0 delta eps : ℝ) (hCg : 0 < Cg)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) (hdelta : delta ≤ E0 / (4 * Cg))
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) (heps : eps ≤ E0 / (4 * Cg)) :
    Cg * (delta ^ 2 + eps ^ 8) + Cg * (E0 / (2 * Cg)) ≤ E0 := by
  have hd0 : delta ^ 2 ≤ delta := by
    nlinarith only [mul_nonneg hdelta0 (sub_nonneg.mpr hdelta1)]
  have hd : delta ^ 2 ≤ E0 / (4 * Cg) := hd0.trans hdelta
  have he : eps ^ 8 ≤ E0 / (4 * Cg) := by
    have h : eps ^ 8 ≤ eps ^ 1 := pow_le_pow_of_le_one heps0 heps1 (by norm_num)
    rw [pow_one] at h
    exact h.trans heps
  have hb : Cg * (delta ^ 2 + eps ^ 8) ≤ Cg * (2 * (E0 / (4 * Cg))) :=
    mul_le_mul_of_nonneg_left (by linarith only [hd, he]) hCg.le
  have hid : Cg * (2 * (E0 / (4 * Cg))) + Cg * (E0 / (2 * Cg)) = E0 := by
    field_simp
    ring
  linarith only [hb, hid]

end SubdiffusiveProcess
