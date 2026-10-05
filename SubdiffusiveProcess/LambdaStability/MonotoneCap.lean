module

public import SubdiffusiveProcess.LambdaStability.WeightedSum
@[expose] public section

open Homogenization
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.LambdaStability

/-- Every shell of a monotone sequence is bounded by the normalized weighted sum. -/
theorem shell_le_rpow_mul_tsum {H : ℕ → ℝ} {s q : ℝ}
    (hsq : 0 < s * q) (hH : ∀ n, 0 ≤ H n) (hmono : Monotone H)
    (hsum : Summable (fun n => geometricWeight s q n * H n)) (j : ℕ) :
    H j ≤ (3 : ℝ) ^ (s * q * (j : ℝ)) * ∑' n, geometricWeight s q n * H n := by
  let f : ℕ → ℝ := fun n => geometricWeight s q n * H n
  have htail : Summable (fun n => f (n + j)) := (summable_nat_add_iff j).2 hsum
  have hshift : (fun n => geometricWeight s q n * H (n + j)) =
      fun n => (3 : ℝ) ^ (s * q * (j : ℝ)) * f (n + j) := by
    funext n
    rw [geometricWeight_shift j n]
    dsimp [f]
    ring
  have hshiftSum : Summable (fun n => geometricWeight s q n * H (n + j)) := by
    rw [hshift]
    exact htail.mul_left _
  have hself : H j ≤ ∑' n, geometricWeight s q n * H (n + j) := by
    simpa only [zero_add] using self_le_tsum_geometricWeight_of_monotone
      (H := fun n => H (n + j)) (fun _ _ h => hmono (Nat.add_le_add_right h j)) hsq hshiftSum
  have htail_le : ∑' n, f (n + j) ≤ ∑' n, f n := by
    have hdecomp := hsum.sum_add_tsum_nat_add j
    have hpref : 0 ≤ ∑ n ∈ Finset.range j, f n := by
      apply Finset.sum_nonneg
      intro n _
      exact mul_nonneg (geometricWeight_nonneg n hsq.le) (hH n)
    dsimp [f] at hpref ⊢
    linarith only [hdecomp, hpref]
  rw [hshift, tsum_mul_left] at hself
  exact hself.trans (mul_le_mul_of_nonneg_left htail_le (Real.rpow_nonneg (by norm_num) _))

end SubdiffusiveProcess.LambdaStability
