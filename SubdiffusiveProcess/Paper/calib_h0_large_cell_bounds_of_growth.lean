module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib_cell_bounds_of_growth
public import SubdiffusiveProcess.Paper.calib_h0_large_cell_bounds
public import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family

@[expose] public section

/-! The harmonic-cell bounds `calib_h0_large_cell_bounds` of a coefficient sequence on the `3^d` cells of a padded cube
from the `prop_growth` conclusion on each cell, with constants uniform along the sequence (Stage 3 assembly). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- **`calib_h0_large_cell_bounds` from cellwise `GrowthAtCoef` with a uniform constant.** -/
theorem calib_h0_large_cell_bounds_of_growth {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (a : ℕ → SpatialCoordinates d → ℝ) (t alpha : ℝ) (ht : 0 ≤ t) (ha : 0 < alpha)
    (hcell : ∀ k : OddGridIndex d (triadicHalf 1), ∃ (A : ℕ → PositiveCoefficient (oddGridCell z R hR (triadicHalf 1) k))
        (K : ℕ → ℝ) (B : ℝ),
      (∀ n, (fun x => (A n).val x) =ᵐ[volume.restrict (oddGridCell z R hR (triadicHalf 1) k : Set (SpatialCoordinates d))] a n) ∧
      (∀ n, K n ≤ B) ∧
      aux_prop_growth_large_root_GrowthAtCoef (oddGridCenter z R (triadicHalf 1) k) (R / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1))
        (div_pos hR (by positivity)) t alpha A K) :
    calib_h0_large_cell_bounds z R hR a t alpha := by
  intro theta htheta thetaH hthetaH k
  obtain ⟨A, K, B, hAa, hK, hG⟩ := hcell k
  exact calib_cell_bounds_of_growth hd (oddGridCenter z R (triadicHalf 1) k) (div_pos hR (by positivity)) A a hAa t alpha
    ht ha K B hK hG theta (htheta.of_le (WithTop.coe_le_coe.mpr le_top))
    (thetaH.restrict (oddGridCell z R hR (triadicHalf 1) k).isOpen (oddGridCell_subset z hR (triadicHalf 1) k)) hthetaH

end
end Paper
