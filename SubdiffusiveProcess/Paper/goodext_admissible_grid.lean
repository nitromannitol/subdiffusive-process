module

public import SubdiffusiveProcess.Paper.goodext_fixed_padding
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Integer-grid coordinates for the density cell bank. -/
def aux_goodext_admissible_grid_centre {d : ℕ} (z0 : SpatialCoordinates d)
    (b : ℕ × (Fin d → ℤ)) : SpatialCoordinates d :=
  fun i => z0 i + (3 : ℝ) ^ (-(b.1 : ℤ)) * b.2 i

/-- Cells whose fixed-enlargement catalogue fits inside the killed cube. -/
def aux_goodext_admissible_grid_cells {d : ℕ} (z0 : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) : Type :=
  {b : ℕ × (Fin d → ℤ) // 1 ≤ b.1 ∧
    ∀ U : Fin 3 × (Fin d → Fin 3),
      closure (centeredCube (gcat_rootCentre 1 b.1 (aux_goodext_admissible_grid_centre z0 b) U)
        (gcat_rootSide 1 b.1 U) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
          (centeredCube z0 R hR : Set (SpatialCoordinates d))}

/-- The actual countable admissible bank is nonempty, consists of contained cells,
and contains every sufficiently deep grid cell padded inside a contained parent. -/
theorem goodext_admissible_grid (d : ℕ) (hd : 1 ≤ d)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    Countable (aux_goodext_admissible_grid_cells z0 R hR) ∧
    Nonempty (aux_goodext_admissible_grid_cells z0 R hR) ∧
    (∀ b : aux_goodext_admissible_grid_cells z0 R hR,
      (centeredCube (aux_goodext_admissible_grid_centre z0 b.val)
        ((3 : ℝ) ^ (-(b.val.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
          (centeredCube z0 R hR : Set (SpatialCoordinates d))) ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (j : Fin d → ℤ) (m : ℕ)
      (zP : SpatialCoordinates d) (digit : OddGridIndex d m),
      aux_goodext_admissible_grid_centre z0 (k, j) =
        oddGridCenter zP ((2 * (m : ℝ) + 1) * (3 : ℝ) ^ (-(k : ℤ))) m digit →
      aux_lem_finite_stopping_partition_padLabel 3 digit →
      Metric.ball zP ((2 * (m : ℝ) + 1) * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
        (centeredCube z0 R hR : Set (SpatialCoordinates d)) →
      ∃ b : aux_goodext_admissible_grid_cells z0 R hR, b.val = (k, j) := by
  classical
  refine ⟨by unfold aux_goodext_admissible_grid_cells; infer_instance, ?_, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < R / 6 by positivity)
      (by norm_num : (1 / 3 : ℝ) < 1)
    have hsmall : (3 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) < R / 6 := by
      have hle : (1 / 3 : ℝ) ^ (n + 1) ≤ (1 / 3 : ℝ) ^ n := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) n]
      simpa only [one_div, inv_pow, zpow_neg, zpow_natCast] using hle.trans_lt hn
    refine ⟨⟨(n + 1, 0), by omega, ?_⟩⟩
    intro U
    have hcentre : aux_goodext_admissible_grid_centre z0 (n + 1, 0) = z0 := by
      funext i
      simp only [aux_goodext_admissible_grid_centre, Pi.zero_apply, Int.cast_zero, mul_zero, add_zero]
    rw [hcentre]
    have hside := aux_affine_source_cells_mass_rootSide_le 1 (n + 1) le_rfl U
    have heq : (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) - (1 : ℤ))) =
        3 * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [show -(((n + 1 : ℕ) : ℤ) - (1 : ℤ)) = 1 + -((n + 1 : ℕ) : ℤ) by ring,
        zpow_add₀ (by norm_num), zpow_one]
    change gcat_rootSide 1 (n + 1) U ≤ (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) - 1)) at hside
    rw [heq] at hside
    exact (aux_affine_source_cells_mass_root_sub 1 (n + 1) z0 U).trans
      (Metric.closedBall_subset_ball (by linarith : gcat_rootSide 1 (n + 1) U < R / 2))
  · intro b
    let U0 : Fin 3 × (Fin d → Fin 3) := (0, fun _ => 1)
    have h := b.property.2 U0
    have hz : gcat_rootCentre 1 b.val.1 (aux_goodext_admissible_grid_centre z0 b.val) U0 =
        aux_goodext_admissible_grid_centre z0 b.val := by
      have hshift : gcat_shift U0.2 = 0 := by
        funext i
        simp only [gcat_shift, U0, Fin.val_one, Nat.cast_one, sub_self, zero_div, Pi.zero_apply]
      simp only [gcat_rootCentre, hshift, smul_zero, add_zero]
    have hs : gcat_rootSide 1 b.val.1 U0 = (3 : ℝ) ^ (-(b.val.1 : ℤ)) := by
      simp only [gcat_rootSide, gcat_rootLevel, gcat_factor, U0,
        Matrix.cons_val_zero, Nat.cast_zero, sub_zero]
    change closure (Metric.ball _ (_ / 2)) ⊆ _ at h
    rw [hz, hs] at h
    exact subset_closure.trans h
  · intro k hk j m zP digit hz hpad hparent
    refine ⟨⟨(k, j), hk, ?_⟩, rfl⟩
    intro U
    have h := (goodext_fixed_padding d hd m).2 zP ((3 : ℝ) ^ (-(k : ℤ)))
      (zpow_pos (by norm_num) _) k rfl digit hpad
    rw [hz]
    exact (h.2 U).trans hparent
end Paper
