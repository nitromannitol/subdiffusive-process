module

public import SubdiffusiveProcess.VariationalResponses.MeshGeometry
public import SubdiffusiveProcess.Sobolev.HarmonicCellError

@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- On a closed odd-grid cell the gradient of `φ` is bounded by its supremum on
the closed parent cube. -/
theorem fderiv_bound_on_cell {φ : SpatialCoordinates d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R) (m : ℕ) (k : OddGridIndex d m)
    {y : SpatialCoordinates d}
    (hy : y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d))) :
    ‖fderiv ℝ φ y‖ ≤
      sSup ((fun q => ‖fderiv ℝ φ q‖) ''
        closure (centeredCube z R hR : Set (SpatialCoordinates d))) :=
  le_sSup_image (isCompact_closure_centeredCube z hR)
    (continuous_norm_fderiv hφ)
    (closure_oddGridCell_subset z hR m k hy)

/-- The gradient supremum on the closed cube is nonnegative. -/
theorem sSup_fderiv_nonneg {φ : SpatialCoordinates d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R) :
    0 ≤ sSup ((fun q => ‖fderiv ℝ φ q‖) ''
      closure (centeredCube z R hR : Set (SpatialCoordinates d))) :=
  sSup_image_norm_nonneg (isCompact_closure_centeredCube z hR)
    ⟨z, subset_closure (Metric.mem_ball_self (half_pos hR))⟩
    (continuous_norm_fderiv hφ) (fun _q => norm_nonneg _)

/-- The frozen mesh target's pointwise clause on one triadic cell, with the
dimensional constant `2 √d` and the cell side `R / 3 ^ J`
(`eq:mfd-18`). -/
theorem mesh_cell_error [NeZero d] (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (J : ℕ) (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam)
    (ha : Continuous a)
    (haBounds : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (k : OddGridIndex d (triadicHalf J))
    (u φ : H1Function
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)))
    (hu : IsWeaklyHarmonicOn a
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u)
    (htrace : HasZeroTraceDifferenceOn
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u φ)
    (hucont : ContinuousOn u.toFun
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)))
    (hφsmooth : ContDiff ℝ ∞ φ.toFun) :
    ∀ x ∈ (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
      |u.toFun x - φ.toFun x| ≤
        2 * Real.sqrt d * (R / (3 : ℝ) ^ J) *
          sSup ((fun q => ‖fderiv ℝ φ.toFun q‖) ''
            closure (centeredCube z R hR : Set (SpatialCoordinates d))) := by
  have hcell := harmonic_cell_error_le (oddGridCenter z R (triadicHalf J) k)
    (R / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) (div_pos hR (by positivity))
    a lam Lam hlam ha
    (fun x hx => haBounds x (oddGridCell_subset z hR (triadicHalf J) k hx))
    u φ hu htrace hucont hφsmooth
    (sSup ((fun q => ‖fderiv ℝ φ.toFun q‖) ''
      closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (sSup_fderiv_nonneg hφsmooth z hR)
    (fun y hy => fderiv_bound_on_cell hφsmooth z hR (triadicHalf J) k hy)
  intro x hx
  refine le_of_le_of_eq (hcell x hx) ?_
  rw [cell_side_eq R J]

end SubdiffusiveProcess
