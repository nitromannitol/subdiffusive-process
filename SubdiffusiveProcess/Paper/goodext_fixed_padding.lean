module

public import SubdiffusiveProcess.Paper.affine_source_cells_mass_roots
public import SubdiffusiveProcess.Paper.lem_finite_stopping_partition_tree
public import SubdiffusiveProcess.FiniteStopping.CellRegularity
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
open Classical

/-- A fixed three-label margin contains the tripled cell and every shifted root
of the fixed-enlargement good-cell catalogue. Its excluded children number at
most 6d L^(d-1), independent of the observation depth. -/
theorem goodext_fixed_padding (d : ℕ) (hd : 1 ≤ d) (m : ℕ) :
    (((Finset.univ : Finset (OddGridIndex d m)).filter
      (fun idx => ¬ aux_lem_finite_stopping_partition_padLabel 3 idx)).card : ℝ) ≤
        (6 * (d : ℝ)) * (2 * (m : ℝ) + 1) ^ ((d : ℝ) - 1) ∧
    ∀ (zP : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (k : ℕ) (hrk : r = (3 : ℝ) ^ (-(k : ℤ))) (idx : OddGridIndex d m),
      aux_lem_finite_stopping_partition_padLabel 3 idx →
      let L : ℝ := 2 * (m : ℝ) + 1
      let z := oddGridCenter zP (L * r) m idx
      Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) ∧
      ∀ U : Fin 3 × (Fin d → Fin 3),
        closure (centeredCube (gcat_rootCentre 1 k z U) (gcat_rootSide 1 k U)
          (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
          Metric.ball zP (L * r / 2) := by
  constructor
  · have hc := aux_lem_finite_stopping_partition_card_not_padLabel_le (d := d) m 3
    have hcr : (((Finset.univ : Finset (OddGridIndex d m)).filter
        (fun idx => ¬ aux_lem_finite_stopping_partition_padLabel 3 idx)).card : ℝ) ≤
        (d : ℝ) * 6 * (2 * (m : ℝ) + 1) ^ (d - 1) := by exact_mod_cast hc
    rw [← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one] at hcr
    nlinarith [hcr]
  · intro zP r hr k hrk idx hpad
    dsimp only
    have hL : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
    have h6 := SubdiffusiveProcess.FiniteStopping.padded_contains zP
      (2 * (m : ℝ) + 1) r hL hr m rfl idx 3 hpad 6 (by norm_num) (by norm_num)
    change Metric.closedBall (oddGridCenter zP ((2 * (m : ℝ) + 1) * r) m idx) (6 * r / 2) ⊆
      Metric.ball zP ((2 * (m : ℝ) + 1) * r / 2) at h6
    constructor
    · exact (Metric.closedBall_subset_closedBall (by linarith : 3 * r / 2 ≤ 6 * r / 2)).trans h6
    · intro U
      have hs := aux_affine_source_cells_mass_rootSide_le 1 k le_rfl U
      have heq : (3 : ℝ) ^ (-((k : ℤ) - (1 : ℤ))) = 3 * r := by
        rw [hrk, show -((k : ℤ) - (1 : ℤ)) = 1 + -(k : ℤ) by ring,
          zpow_add₀ (by norm_num), zpow_one]
      change gcat_rootSide 1 k U ≤ (3 : ℝ) ^ (-((k : ℤ) - 1)) at hs
      rw [heq] at hs
      exact (aux_affine_source_cells_mass_root_sub 1 k _ U).trans
        ((Metric.closedBall_subset_closedBall (by linarith : gcat_rootSide 1 k U ≤ 6 * r / 2)).trans h6)

end SubdiffusiveProcess.Paper
