module

public import SubdiffusiveProcess.Geometry.PrefixRootCatalogue

@[expose] public section

/-! Projecting a point of the unit triadic mesh onto any collection of cube
faces gives a root in the same padded catalogue. This identifies the exact
centres used by the deterministic two-mesh estimate.
-/
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- Every projected unit-grid point with an admitted radius index lies in the padded root catalogue. -/
theorem projected_grid_mem_prefixRootCatalogue {d : ℕ} (n J k : ℕ) (hk : k ≤ n + J)
    (g : Fin d → Fin (3 ^ (n + J) + 1)) (I : Finset (Fin d)) :
    ∃ p ∈ prefixRootCatalogue d 1 J n,
      prefixRootLevel J p = (k : ℤ) - J ∧
      prefixRootCentre J p = fun i =>
        if i ∈ I then
          (if ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-((n + J : ℕ) : ℤ)) ≤ 1 / 2 then 0 else 1)
        else ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-((n + J : ℕ) : ℤ)) := by
  classical
  let idx : Fin d → ℤ := fun i => if i ∈ I then
    (if ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-((n + J : ℕ) : ℤ)) ≤ 1 / 2
      then 0 else (3 ^ (n + J) : ℕ)) else (g i : ℕ)
  have hidx : idx ∈ gridIndices d 1 (n + J) := by
    rw [gridIndices, Fintype.mem_piFinset]
    intro i
    have hceil : ⌈(3 : ℝ) ^ ((n + J : ℕ) : ℤ)⌉ = (3 ^ (n + J) : ℕ) := by
      have heq : (3 : ℝ) ^ (n + J) = ((3 ^ (n + J) : ℕ) : ℝ) := by norm_cast
      rw [zpow_natCast, heq, Int.ceil_natCast]
    simp only [one_mul, hceil, Finset.mem_Icc]
    have hg : (g i : ℕ) ≤ 3 ^ (n + J) := Nat.le_of_lt_succ (g i).isLt
    dsimp only [idx]
    split_ifs <;> constructor <;> omega
  refine ⟨(n, idx, k), (mem_prefixRootCatalogue 1 J n _).mpr ⟨rfl, hidx, hk⟩, rfl, ?_⟩
  funext i
  dsimp only [prefixRootCentre, gridPoint, idx]
  by_cases hi : i ∈ I
  · rw [if_pos hi, if_pos hi]
    split_ifs with h
    · norm_num
    · norm_num only [Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
  · simp only [if_neg hi, Int.cast_natCast]

end SubdiffusiveProcess
