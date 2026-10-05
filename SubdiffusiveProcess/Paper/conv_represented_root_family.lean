module

public import Mathlib
public import SubdiffusiveProcess.Geometry.RationalTriadicCatalogue

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Rooted catalogue family.**  The family `(Z i, R i)` is exactly the family of the rational-centred cubes with
triadic sides that lie inside one ROOT member `(Z j0, R j0)` containing the unit cube: every member is inside the root,
and every rational-centred triadic cube inside the root occurs as some member.  (This is the geometry that clause C of
`conv_represented_estimates` records for a single root; the global family "all rational triadic cubes of `R^d`" of
`conv_represented_catalogue_geometry` is the union of the roots `(0, 3^m)`.) -/
def conv_represented_root_family (d : ℕ) (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ)
    (hR : ∀ i, 0 < R i) : Prop :=
  ∃ j0 : ℕ,
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ⊆
      (centeredCube (Z j0) (R j0) (hR j0) : Set (SpatialCoordinates d)) ∧
    (∀ i, (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (Z j0) (R j0) (hR j0) : Set (SpatialCoordinates d))) ∧
    (∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) → (∃ m : ℤ, r' = (3 : ℝ) ^ m) →
      (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube (Z j0) (R j0) (hR j0) : Set (SpatialCoordinates d)) →
      ∃ i, Z i = z' ∧ R i = r')

end SubdiffusiveProcess.Paper
