import SubdiffusiveProcess.Section6SumErrors.StoppingIndex
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ErrorStoppingAnalytic
/-!
# GeometricTail

The reverse starting-scale geometric sum, retaining the first lattice step in its exponential rate.
-/

namespace SubdiffusiveProcess.Section6SumErrors
open MeasureTheory
open scoped BigOperators
noncomputable section

/-- The starting-scale union retains `q`, rather than losing one lattice step. -/
theorem sum_reverse_exp_le {u : ℝ} (hu : 1 ≤ u) (q m : ℕ) (hqm : q ≤ m) :
    (∑ n ∈ Finset.range (m - q + 1),
      Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ))))) ≤
      2 * Real.exp (-(u ^ 2 * (q : ℝ))) := by
  let R := u ^ 2
  let f : ℕ → ℝ := fun j => Real.exp (-R * ((q : ℝ) + j))
  have hR : 1 ≤ R := by dsimp only [R]; nlinarith
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hr0 : 0 ≤ Real.exp (-R) := (Real.exp_pos _).le
  have hr1 : Real.exp (-R) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hRpos)
  have heq : ∀ j : ℕ, f j = Real.exp (-R * q) * Real.exp (-R) ^ j := by
    intro j
    dsimp only [f]
    rw [← Real.exp_nat_mul (-R) j, ← Real.exp_add]
    congr 1
    ring
  have hf : Summable f := by
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-R * q))).congr
      (fun j => (heq j).symm)
  have hreflect : (∑ n ∈ Finset.range (m - q + 1),
      Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ))))) =
      ∑ j ∈ Finset.range (m - q + 1), f j := by
    rw [← Finset.sum_range_reflect (fun n => Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ))))) (m - q + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hN : m - q + 1 - 1 - j = m - q - j := by omega
    rw [hN, Nat.cast_sub (by omega : j ≤ m - q), Nat.cast_sub hqm]
    dsimp only [f, R]
    congr 1
    ring
  have hexp : Real.exp (-R) ≤ (1 / 2 : ℝ) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hR)).trans
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
    nlinarith [Real.exp_one_gt_d9]
  have hden : 0 < 1 - Real.exp (-R) := by linarith
  have hinv : (1 - Real.exp (-R))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  rw [hreflect]
  calc
    _ ≤ ∑' j, f j := hf.sum_le_tsum _ (fun j _ => (Real.exp_pos _).le)
    _ = Real.exp (-R * q) * (1 - Real.exp (-R))⁻¹ := by
      rw [tsum_congr heq, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ Real.exp (-R * q) * 2 := mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
    _ = _ := by dsimp only [R]; rw [mul_comm]; congr 2; ring

end
end SubdiffusiveProcess.Section6SumErrors
