import SubdiffusiveProcess.Geometry.TriadicResidual
import Mathlib.Tactic

/-!
# Actual odd cells in the represented triadic catalogue

A rational-centred triadic root has rational-centred triadic odd-grid children.
Catalogue completeness therefore supplies an index for each physical child.
-/

open SubdiffusiveProcess
noncomputable section
namespace Paper

private theorem rational_odd_center {d : ℕ}
    (z0 : SpatialCoordinates d) (R : ℝ)
    (hz : ∀ i : Fin d, ∃ q : ℚ, z0 i = (q : ℝ))
    (hR : ∃ e : ℤ, R = (3 : ℝ) ^ e)
    (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)) :
    ∀ i : Fin d, ∃ q : ℚ,
      oddGridCenter z0 R (triadicHalf Jr) k i = (q : ℝ) := by
  intro i
  obtain ⟨qz, hqz⟩ := hz i
  obtain ⟨e, he⟩ := hR
  refine ⟨qz + (((k i).val : ℚ) - (triadicHalf Jr : ℚ)) *
      ((3 : ℚ) ^ e / (3 : ℚ) ^ Jr), ?_⟩
  simp only [oddGridCenter, hqz, he, triadic_denominator]
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast,
    Rat.cast_zpow, Rat.cast_div, Rat.cast_pow]
  norm_num

private theorem rational_odd_radius (R : ℝ)
    (hR : ∃ e : ℤ, R = (3 : ℝ) ^ e) (Jr : ℕ) :
    ∃ e : ℤ, R / (3 : ℝ) ^ Jr = (3 : ℝ) ^ e := by
  obtain ⟨e, he⟩ := hR
  refine ⟨e - Jr, ?_⟩
  rw [he, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]

theorem aux_cutoffs_odd_cell_catalogue_of_geometry {d : ℕ} {J : Type} (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hrad : ∀ j, 0 < rad j)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hz0 : z j0 = z0) (hrad0 : rad j0 = R)
    (hcenter : ∀ (j : J) (i : Fin d), ∃ q : ℚ, z j i = (q : ℝ))
    (hscale : ∀ j : J, ∃ e : ℤ, rad j = (3 : ℝ) ^ e)
    (hcomplete : ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) →
      (∃ e : ℤ, r' = (3 : ℝ) ^ e) →
      (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) →
      ∃ j : J, z j = z' ∧ rad j = r')
    (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)) :
    ∃ j_cell : J,
      z j_cell = oddGridCenter z0 R (triadicHalf Jr) k ∧
      rad j_cell = R / (3 : ℝ) ^ Jr := by
  let r' := R / (2 * (triadicHalf Jr : ℝ) + 1)
  have hr' : 0 < r' := div_pos hR (by positivity)
  have hz : ∀ i : Fin d, ∃ q : ℚ,
      oddGridCenter z0 R (triadicHalf Jr) k i = (q : ℝ) :=
    rational_odd_center z0 R (fun i => hz0 ▸ hcenter j0 i)
      (hrad0 ▸ hscale j0) Jr k
  have hs : ∃ e : ℤ, r' = (3 : ℝ) ^ e := by
    dsimp [r']
    rw [triadic_denominator]
    exact rational_odd_radius R (hrad0 ▸ hscale j0) Jr
  obtain ⟨j, hjz, hjr⟩ := hcomplete _ _ hr' hz hs (by
    change (oddGridCell z0 R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)) ⊆ _
    simpa only [← hz0, ← hrad0] using
      oddGridCell_subset z0 hR (triadicHalf Jr) k)
  refine ⟨j, hjz, ?_⟩
  simpa only [r', triadic_denominator] using hjr

end Paper
