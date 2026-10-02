import SubdiffusiveProcess.Geometry.CoordinateFold

/-! Coordinate reflection commutes with positive dilation. These identities
identify the physical and native folded coefficients, without a PDE assertion.
-/
noncomputable section
namespace SubdiffusiveProcess

/-- Positive dilation commutes with folding the corresponding scaled root. -/
theorem coordinateFold_smul {d : ℕ} (l : ℝ) (hl : 0 ≤ l)
    (z x : SpatialCoordinates d) (I P : Finset (Fin d)) :
    coordinateFold (l • z) I P (l • x) = l • coordinateFold z I P x := by
  funext i
  by_cases hi : i ∈ I
  · simp only [coordinateFold, hi, if_true, Pi.smul_apply, smul_eq_mul,
      ← mul_sub, abs_mul, abs_of_nonneg hl]
    ring
  · simp only [coordinateFold, hi, if_false, Pi.smul_apply, smul_eq_mul]

/-- Pulling a folded native chart back by a positive dilation gives the physical chart. -/
theorem inv_smul_coordinateFold_add {d : ℕ} (l : ℝ) (hl : 0 < l)
    (z x : SpatialCoordinates d) (I P : Finset (Fin d)) :
    l⁻¹ • coordinateFold (l • z) I P (x + l • z) =
      coordinateFold z I P (l⁻¹ • x + z) := by
  rw [show x + l • z = l • (l⁻¹ • x + z) by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hl.ne', one_smul],
    coordinateFold_smul l hl.le, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]

end SubdiffusiveProcess
