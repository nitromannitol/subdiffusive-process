module

public import SubdiffusiveProcess.Paper.density_descendant_grid
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- All contained integer-grid cells, including cells whose enlargement meets the boundary. -/
def aux_density_full_grid_cells {d : ℕ} (z0 : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) : Type :=
  {b : ℕ × (Fin d → ℤ) //
    (centeredCube (aux_goodext_admissible_grid_centre z0 b)
      ((3 : ℝ) ^ (-(b.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z0 R hR : Set (SpatialCoordinates d))}

/-- The harmonic bank must cover every contained cell. Admissible good cells
embed in that bank, and every contained observation descendant has its exact
absolute level and centre there. No enlargement condition is imposed on residual cells. -/
theorem density_full_grid {d : ℕ} (hd : 1 ≤ d)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    Countable (aux_density_full_grid_cells z0 R hR) ∧
    Nonempty (aux_density_full_grid_cells z0 R hR) ∧
    (∃ embed : aux_goodext_admissible_grid_cells z0 R hR → aux_density_full_grid_cells z0 R hR,
      Function.Injective embed ∧ ∀ b, (embed b).val = b.val) ∧
    ∀ (H1 : ℕ) (zroot : SpatialCoordinates d) (jroot : Fin d → ℤ),
      zroot = (fun i => z0 i + (jroot i : ℝ)) →
      ∀ n (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
        (descendantCell (subdivisionHalfWidth H1) zroot (by norm_num : (0 : ℝ) < 1) n w :
          Set (SpatialCoordinates d)) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)) →
        ∃ b : aux_density_full_grid_cells z0 R hR,
          b.val.1 = H1 * n ∧
          aux_goodext_admissible_grid_centre z0 b.val =
            descendantCenter (subdivisionHalfWidth H1) zroot 1 n w ∧
          (centeredCube (aux_goodext_admissible_grid_centre z0 b.val)
            ((3 : ℝ) ^ (-(b.val.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) =
            (descendantCell (subdivisionHalfWidth H1) zroot (by norm_num : (0 : ℝ) < 1) n w :
              Set (SpatialCoordinates d)) := by
  classical
  have hAd := goodext_admissible_grid d hd z0 R hR
  let embed : aux_goodext_admissible_grid_cells z0 R hR → aux_density_full_grid_cells z0 R hR :=
    fun b => ⟨b.val, hAd.2.2.1 b⟩
  obtain ⟨first⟩ := hAd.2.1
  refine ⟨by unfold aux_density_full_grid_cells; infer_instance, ⟨embed first⟩,
    ⟨embed, ?_, fun _ => rfl⟩, ?_⟩
  · intro a b hab
    exact Subtype.ext (congrArg (fun x : aux_density_full_grid_cells z0 R hR => x.val) hab)
  · intro H1 zroot jroot hroot n w hsub
    obtain ⟨j, hj⟩ := density_descendant_grid H1 z0 zroot jroot hroot n w
    have hside : descendantSide (subdivisionHalfWidth H1) n (1 : ℝ) =
        (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)) := by
      have h := FiniteStopping.descendantSide_zpow H1 (subdivisionHalfWidth H1)
        (two_mul_subdivisionHalfWidth_add_one H1) 0 n
      simpa only [zpow_zero, zero_sub] using h
    have hcell : (centeredCube (aux_goodext_admissible_grid_centre z0 (H1 * n, j))
        ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) =
        (descendantCell (subdivisionHalfWidth H1) zroot (by norm_num : (0 : ℝ) < 1) n w :
          Set (SpatialCoordinates d)) := by
      change Metric.ball _ _ = Metric.ball _ _
      rw [hj, hside]
    exact ⟨⟨(H1 * n, j), hcell ▸ hsub⟩, rfl, hj.symm, hcell⟩
end Paper
