import SubdiffusiveProcess.Analysis.NativeScoreAllowance
import SubdiffusiveProcess.Analysis.AffineAllowanceProduct
import SubdiffusiveProcess.Geometry.ProjectedPrefixRoots

/-! An affine bound on the actual finite score allowance controls the complete
two-mesh exponential factor, including every boundary projection. This is a
deterministic composition and asserts no stochastic prefix bound.
-/
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- The actual finite allowance at a resolved root, set to zero beyond the cutoff. -/
def nativeCutoffRootAllowance {d : ℕ} (Z : ℕ → SpatialCoordinates d → ℝ)
    (D : ℕ → SpatialCoordinates d → ℝ≥0∞) (N k : ℕ) (rate : ℝ)
    (z : SpatialCoordinates d) : ℝ :=
  if k ≤ N then (nativeScoreAllowance (fun j => Z j ((3 : ℝ) ^ N • z))
    (fun j => D j ((3 : ℝ) ^ N • z)) (N - k + 1) rate : ℝ) else 0

/-- Every actual cutoff root allowance is nonnegative. -/
theorem nativeCutoffRootAllowance_nonneg {d : ℕ} (Z : ℕ → SpatialCoordinates d → ℝ)
    (D : ℕ → SpatialCoordinates d → ℝ≥0∞) (N k : ℕ) (rate : ℝ)
    (z : SpatialCoordinates d) : 0 ≤ nativeCutoffRootAllowance Z D N k rate z := by
  unfold nativeCutoffRootAllowance
  split_ifs <;> positivity

/-- The exact boundary-projected mesh factor is bounded by the common allowance intercept. -/
theorem native_mesh_allowance_le {d : ℕ} (Z : ℕ → SpatialCoordinates d → ℝ)
    (D : ℕ → SpatialCoordinates d → ℝ≥0∞) (N : ℕ) (rate xi B eta c C : ℝ)
    (hxi : 0 ≤ xi) (hB : 0 ≤ B) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hgap : c * (d + 1 : ℕ) * xi ≤ eta * Real.log 3)
    (hroot : ∀ (n : ℕ) (p : PrefixRootIndex d), p ∈ prefixRootCatalogue d 1 1 n →
      prefixRootLevel 1 p ≤ (N : ℤ) →
      (nativeScoreAllowance (fun j => Z j ((3 : ℝ) ^ N • prefixRootCentre 1 p))
        (fun j => D j ((3 : ℝ) ^ N • prefixRootCentre 1 p))
          ((N : ℤ) - prefixRootLevel 1 p).toNat rate : ℝ) ≤ xi * n + B)
    (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
    (dep : Fin (d + 1) → Fin (n + 1 + 1)) (sigma : Equiv.Perm (Fin d)) :
    (3 : ℝ) ^ (-eta * (n : ℝ)) * (C ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
      nativeCutoffRootAllowance Z D N (dep j).val rate (fun i =>
        if i ∈ (Finset.univ.filter (fun i : Fin d => (sigma.symm i).val < j.val)) then
          (if ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) ≤ 1 / 2 then 0 else 1)
        else ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))))) ≤
      C ^ (d + 1) * Real.exp (c * (d + 1 : ℕ) * B) := by
  classical
  have hprod (b : Fin (d + 1) → ℝ) (hb : ∀ j, b j ≤ xi * n + B) :
      (3 : ℝ) ^ (-eta * (n : ℝ)) * (C ^ (d + 1) * Real.exp (c * ∑ j, b j)) ≤
        C ^ (d + 1) * Real.exp (c * (d + 1 : ℕ) * B) := by
    simpa only [Fintype.card_fin] using discounted_allowance_product_le b n xi B eta c
      (C ^ (d + 1)) hc (pow_nonneg hC _) hb (by simpa only [Fintype.card_fin] using hgap)
  apply hprod
  intro j
  unfold nativeCutoffRootAllowance
  split_ifs with hkN
  · obtain ⟨p, hp, hlev, hctr⟩ := projected_grid_mem_prefixRootCatalogue n 1 (dep j).val
      (Nat.le_of_lt_succ (dep j).isLt) g
      (Finset.univ.filter (fun i : Fin d => (sigma.symm i).val < j.val))
    have hpN : prefixRootLevel 1 p ≤ (N : ℤ) := by rw [hlev]; omega
    have hh := hroot n p hp hpN
    have hidx : ((N : ℤ) - prefixRootLevel 1 p).toNat = N - (dep j).val + 1 := by rw [hlev]; omega
    rw [hidx, hctr] at hh
    exact hh
  · exact add_nonneg (mul_nonneg hxi (Nat.cast_nonneg _)) hB

end SubdiffusiveProcess
