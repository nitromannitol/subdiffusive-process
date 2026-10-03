module

public import SubdiffusiveProcess.Paper.density_full_grid
public import SubdiffusiveProcess.Paper.density_grid_descendants
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Absolute level and centre identify an integer-grid cell uniquely. -/
lemma aux_density_based_full_grid_index_ext {d : ℕ} (z0 : SpatialCoordinates d)
    (b c : ℕ × (Fin d → ℤ)) (hk : b.1 = c.1)
    (hz : aux_goodext_admissible_grid_centre z0 b = aux_goodext_admissible_grid_centre z0 c) :
    b = c := by
  apply Prod.ext hk
  funext i
  have hi := congrFun hz i
  dsimp only [aux_goodext_admissible_grid_centre] at hi
  rw [hk] at hi
  have hj : (b.2 i : ℝ) = (c.2 i : ℝ) :=
    mul_left_cancel₀ (zpow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)) (add_left_cancel hi)
  exact Int.cast_inj.mp hj

/-- Every descendant of a contained absolute-grid base has its exact full-bank
index. On active descendants this index agrees with any admissible index having
the already-proved level and centre. -/
theorem density_based_full_grid {d : ℕ} (H1 base : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (zroot : SpatialCoordinates d) (jroot : Fin d → ℤ)
    (hroot : zroot = fun i => z0 i + (3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ)) * (jroot i : ℝ))
    (hsub : (centeredCube zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ)))
      (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z0 R hR : Set (SpatialCoordinates d))) :
    let m := subdivisionHalfWidth H1
    let r := (3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))
    ∃ index : (n : ℕ) → (Fin n → OddGridIndex d m) → aux_density_full_grid_cells z0 R hR,
      ∀ n w,
        (index n w).val.1 = H1 * (base + n) ∧
        aux_goodext_admissible_grid_centre z0 (index n w).val = descendantCenter m zroot r n w ∧
        (3 : ℝ) ^ (-((index n w).val.1 : ℤ)) = descendantSide m n r ∧
        centeredCube (aux_goodext_admissible_grid_centre z0 (index n w).val)
          ((3 : ℝ) ^ (-((index n w).val.1 : ℤ))) (zpow_pos (by norm_num) _) =
            descendantCell m zroot (show 0 < r from zpow_pos (by norm_num) _) n w ∧
        ∀ b : aux_goodext_admissible_grid_cells z0 R hR,
          b.val.1 = H1 * (base + n) →
          aux_goodext_admissible_grid_centre z0 b.val = descendantCenter m zroot r n w →
          (index n w).val = b.val := by
  classical
  intro m r
  have hr : 0 < r := zpow_pos (by norm_num) _
  have hside : ∀ n, descendantSide m n r = (3 : ℝ) ^ (-((H1 * (base + n) : ℕ) : ℤ)) := by
    intro n
    have h := FiniteStopping.descendantSide_zpow H1 m
      (two_mul_subdivisionHalfWidth_add_one H1) (-((H1 * base : ℕ) : ℤ)) n
    exact h.trans (by congr 1; push_cast; ring)
  have hex : ∀ n (w : Fin n → OddGridIndex d m), ∃ b : aux_density_full_grid_cells z0 R hR,
      b.val.1 = H1 * (base + n) ∧
      aux_goodext_admissible_grid_centre z0 b.val = descendantCenter m zroot r n w ∧
      (3 : ℝ) ^ (-(b.val.1 : ℤ)) = descendantSide m n r ∧
      centeredCube (aux_goodext_admissible_grid_centre z0 b.val)
        ((3 : ℝ) ^ (-(b.val.1 : ℤ))) (zpow_pos (by norm_num) _) =
          descendantCell m zroot hr n w := by
    intro n w
    obtain ⟨j, hj⟩ := density_grid_descendants H1 (H1 * base) z0 zroot jroot hroot n w
    rw [← Nat.mul_add] at hj
    have heq : centeredCube (aux_goodext_admissible_grid_centre z0 (H1 * (base + n), j))
        ((3 : ℝ) ^ (-((H1 * (base + n) : ℕ) : ℤ))) (zpow_pos (by norm_num) _) =
          descendantCell m zroot hr n w := by
      apply TopologicalSpace.Opens.ext
      change Metric.ball _ _ = Metric.ball _ _
      rw [← hj, ← hside]
    have hcontained : (centeredCube (aux_goodext_admissible_grid_centre z0 (H1 * (base + n), j))
        ((3 : ℝ) ^ (-((H1 * (base + n) : ℕ) : ℤ))) (zpow_pos (by norm_num) _) :
        Set (SpatialCoordinates d)) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)) := by
      rw [heq]
      exact (aux_lem_finite_stopping_partition_descendantCell_subset_root m zroot hr n w).trans hsub
    exact ⟨⟨(H1 * (base + n), j), hcontained⟩, rfl, hj.symm, (hside n).symm, heq⟩
  choose index hlevel hcentre hrad hcell using hex
  refine ⟨index, fun n w => ⟨hlevel n w, hcentre n w, hrad n w, hcell n w, ?_⟩⟩
  intro b hb hc
  exact aux_density_based_full_grid_index_ext z0 (index n w).val b.val
    ((hlevel n w).trans hb.symm) ((hcentre n w).trans hc.symm)
end Paper
