module

public import SubdiffusiveProcess.Geometry.BoundaryPartitions

@[expose] public section

/-! A triadic root's centered subdivision is an absolute translated triadic grid.
No coefficient estimate is asserted. -/
open Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess

/-- The labeled grid side is the quotient of the root side by its triadic depth. -/
theorem triadicGridSide_eq_div_pow {d : ℕ} (R : ℝ) (q : TriadicGridLabel d) :
    triadicGridSide R q = R / (3 : ℝ) ^ q.1 := by
  have hden : 2 * (triadicHalf q.1 : ℝ) + 1 = (3 : ℝ) ^ q.1 := by
    exact_mod_cast two_mul_triadicHalf_add_one q.1
  exact congrArg (fun a : ℝ => R / a) hden

/-- A triadic root makes every subdivision side an integral power of three. -/
theorem triadicGridSide_eq_zpow {d : ℕ} (R : ℝ) (ell : ℤ)
    (hR : R = (3 : ℝ) ^ ell) (q : TriadicGridLabel d) :
    triadicGridSide R q = (3 : ℝ) ^ (ell - (q.1 : ℤ)) := by
  rw [triadicGridSide_eq_div_pow, hR, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]

/-- A labeled center is the root center plus an integer multiple of its cell side. -/
theorem triadicGridCenter_eq_int_shift {d : ℕ} (z : SpatialCoordinates d) (R : ℝ)
    (q : TriadicGridLabel d) :
    triadicGridCenter z R q = fun i => z i + triadicGridSide R q *
      (((q.2 i).val : ℤ) - (triadicHalf q.1 : ℤ)) := by
  funext i
  simp only [triadicGridCenter, oddGridCenter, triadicGridSide, Int.cast_sub, Int.cast_natCast]
  ring

/-- Beyond the root's nonnegative exponent, each cell has an absolute nonnegative grid level. -/
theorem triadicGrid_absolute_level {d : ℕ} (z : SpatialCoordinates d) (R : ℝ)
    (ell : ℤ) (hR : R = (3 : ℝ) ^ ell) (q : TriadicGridLabel d)
    (hq : ell.toNat ≤ q.1) :
    ∃ k : ℕ, triadicGridSide R q = (3 : ℝ) ^ (-(k : ℤ)) ∧
      triadicGridCenter z R q = fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) *
        (((q.2 i).val : ℤ) - (triadicHalf q.1 : ℤ)) := by
  have hnonneg : 0 ≤ (q.1 : ℤ) - ell := by omega
  let k : ℕ := ((q.1 : ℤ) - ell).toNat
  have hk : (k : ℤ) = (q.1 : ℤ) - ell := Int.toNat_of_nonneg hnonneg
  have hside : triadicGridSide R q = (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [triadicGridSide_eq_zpow R ell hR q, hk]
    congr 1
    omega
  refine ⟨k, hside, ?_⟩
  rw [triadicGridCenter_eq_int_shift, hside]

/-- The admissible absolute-grid cells have side at most one. -/
theorem triadicGridSide_le_one {d : ℕ} (R : ℝ) (ell : ℤ)
    (hR : R = (3 : ℝ) ^ ell) (q : TriadicGridLabel d) (hq : ell.toNat ≤ q.1) :
    triadicGridSide R q ≤ 1 := by
  rw [triadicGridSide_eq_zpow R ell hR q]
  exact zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)

end SubdiffusiveProcess
