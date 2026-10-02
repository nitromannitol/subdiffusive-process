import SubdiffusiveProcess.Geometry.TriadicNesting
import SubdiffusiveProcess.Geometry.ClosedOddGridCover

/-! Labels and geometric data for finite triadic refinements near a cube boundary.
No existence of these partitions or analytic extension theorem is asserted here. -/
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess
attribute [local instance] Classical.propDecidable

/-- A cube in the centered triadic subdivision of a fixed root. -/
abbrev TriadicGridLabel (d : ℕ) := Σ n : ℕ, OddGridIndex d (triadicHalf n)

/-- The center of a labeled cube in the fixed root grid. -/
def triadicGridCenter {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (q : TriadicGridLabel d) :
    SpatialCoordinates d := oddGridCenter z R (triadicHalf q.1) q.2

/-- The side length of a labeled cube in the fixed root grid. -/
def triadicGridSide {d : ℕ} (R : ℝ) (q : TriadicGridLabel d) : ℝ :=
  R / (2 * (triadicHalf q.1 : ℝ) + 1)

/-- All labeled grid cubes have positive side length when their root does. -/
theorem triadicGridSide_pos {d : ℕ} {R : ℝ} (hR : 0 < R) (q : TriadicGridLabel d) :
    0 < triadicGridSide R q := div_pos hR (by positivity)

/-- The actual open cube associated with a root-grid label. -/
def triadicGridCell {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (q : TriadicGridLabel d) : Opens (SpatialCoordinates d) :=
  centeredCube (triadicGridCenter z R q) (triadicGridSide R q) (triadicGridSide_pos hR q)

/-- Each labeled grid cube is contained in the original root. -/
theorem triadicGridCell_subset {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (q : TriadicGridLabel d) :
    (triadicGridCell z R hR q : Set (SpatialCoordinates d)) ⊆ centeredCube z R hR :=
  oddGridCell_subset z hR (triadicHalf q.1) q.2

/-- Finite compatible refinements, their persistent cells, and their geometric packing bounds. -/
structure TriadicBoundaryPartitions {d : ℕ}
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (B : Set (SpatialCoordinates d)) (r s C : ℝ) (minLevel : ℕ) where
  /-- Number of leaves at each finite horizon. -/
  count : ℕ → ℕ
  /-- Actual root-grid labels of the leaves. -/
  label : ∀ n, Fin (count n) → TriadicGridLabel d
  /-- Every leaf refines the fixed allowed base grid. -/
  depth_ge : ∀ n i, minLevel ≤ (label n i).1
  /-- Distinct leaves have disjoint interiors. -/
  disjoint : ∀ n, Pairwise (fun i j => Disjoint
    (triadicGridCell z R hR (label n i) : Set (SpatialCoordinates d))
    (triadicGridCell z R hR (label n j) : Set (SpatialCoordinates d)))
  /-- Closed leaves cover the closed root exactly. -/
  cover : ∀ n, (⋃ i, closure (triadicGridCell z R hR (label n i) : Set (SpatialCoordinates d))) =
    closure (centeredCube z R hR : Set (SpatialCoordinates d))
  /-- Open leaves cover the root up to Lebesgue null sets. -/
  cover_ae : ∀ n, (⋃ i, (triadicGridCell z R hR (label n i) : Set (SpatialCoordinates d))) =ᵐ[volume]
    (centeredCube z R hR : Set (SpatialCoordinates d))
  /-- Cells touching the target boundary become uniformly small. -/
  boundary : ∀ n x, x ∈ frontier B → ∃ i,
    x ∈ closure (triadicGridCell z R hR (label n i) : Set (SpatialCoordinates d)) ∧
      triadicGridSide R (label n i) ≤ r * (3 : ℝ) ^ (-(n : ℤ))
  /-- Later refinements either preserve a containing cell or use small containing cells at both horizons. -/
  persistence : ∀ n m, n ≤ m → ∀ x,
    x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
    (∃ i j, label n i = label m j ∧
      x ∈ closure (triadicGridCell z R hR (label n i) : Set (SpatialCoordinates d))) ∨
    (∃ i j,
      x ∈ closure (triadicGridCell z R hR (label n i) : Set (SpatialCoordinates d)) ∧
      x ∈ closure (triadicGridCell z R hR (label m j) : Set (SpatialCoordinates d)) ∧
      triadicGridSide R (label n i) ≤ r * (3 : ℝ) ^ (-(n : ℤ)) ∧
      triadicGridSide R (label m j) ≤ r * (3 : ℝ) ^ (-(n : ℤ)))
  /-- The total geometric cost is bounded uniformly in the refinement horizon. -/
  total : ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ∑ i, (triadicGridSide R (label n i)) ^ s ≤ K
  /-- Only cells meeting the open target contribute to its packing bound. -/
  local_bound : ∀ n, ∑ i, (if ((triadicGridCell z R hR (label n i) : Set (SpatialCoordinates d)) ∩ B).Nonempty
    then (triadicGridSide R (label n i)) ^ s else 0) ≤ C * r ^ s

end SubdiffusiveProcess
