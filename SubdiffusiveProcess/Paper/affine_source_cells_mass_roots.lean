module

public import SubdiffusiveProcess.Paper.affine_source_cells_env
public import Mathlib.Tactic

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper
/-- The gcat shifts are at most `1/2` in every coordinate. -/
theorem aux_affine_source_cells_mass_shift_le {d : ℕ} (t : Fin d → Fin 3) (i : Fin d) :
    |gcat_shift t i| ≤ 1 / 2 := by
  unfold gcat_shift
  have h : (t i : ℕ) < 3 := (t i).isLt
  rw [abs_le]
  have h0 : (0 : ℝ) ≤ ((t i : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : ((t i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : (t i : ℕ) ≤ 2)
  constructor <;> linarith

/-- The closure of a root cube is inside the closed ball of radius equal to its side around the concentric
centre `z` (the shifts are at most `1/2`). -/
theorem aux_affine_source_cells_mass_root_sub {d : ℕ} (gH k : ℕ) (z : SpatialCoordinates d)
    (U : Fin 3 × (Fin d → Fin 3)) :
    closure (centeredCube (gcat_rootCentre gH k z U) (gcat_rootSide gH k U)
      (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
      Metric.closedBall z (gcat_rootSide gH k U) := by
  have hs : 0 < gcat_rootSide gH k U := zpow_pos (by norm_num) _
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  change x ∈ Metric.ball (gcat_rootCentre gH k z U) (gcat_rootSide gH k U / 2) at hx
  rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)] at hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hs.le]
  intro i
  have h1 := hx i
  rw [Real.dist_eq, abs_lt] at h1
  rw [Real.dist_eq, abs_le]
  have hsh := aux_affine_source_cells_mass_shift_le U.2 i
  rw [abs_le] at hsh
  have hc : gcat_rootCentre gH k z U i = z i + gcat_rootSide gH k U * gcat_shift U.2 i := rfl
  rw [hc] at h1
  constructor <;> nlinarith [h1.1, h1.2, hsh.1, hsh.2]

/-- The side of every root is at most the side of the enlargement-`gH` root. -/
theorem aux_affine_source_cells_mass_rootSide_le {d : ℕ} (gH k : ℕ) (hgH : 1 ≤ gH)
    (U : Fin 3 × (Fin d → Fin 3)) :
    gcat_rootSide gH k U ≤ (3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))) := by
  unfold gcat_rootSide gcat_rootLevel
  apply zpow_le_zpow_right₀ (by norm_num)
  have h : gcat_factor gH U.1 ≤ gH := by
    unfold gcat_factor
    have : ∀ j : Fin 3, (![0, 1, gH] : Fin 3 → ℕ) j ≤ gH := by
      intro j
      fin_cases j <;> simp <;> omega
    exact this U.1
  have h' : ((gcat_factor gH U.1 : ℕ) : ℤ) ≤ (gH : ℤ) := by exact_mod_cast h
  linarith




theorem affine_source_cells_mass_roots {d : ℕ} (gH k : ℕ) (z : SpatialCoordinates d)
    (U : Fin 3 × (Fin d → Fin 3)) :
    closure (centeredCube (gcat_rootCentre gH k z U) (gcat_rootSide gH k U)
      (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
      Metric.closedBall z (gcat_rootSide gH k U) :=
  aux_affine_source_cells_mass_root_sub gH k z U

end Paper
end
