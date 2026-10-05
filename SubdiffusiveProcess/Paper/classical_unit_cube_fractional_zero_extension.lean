module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Analysis.CubeFractionalZeroExtension

@[expose] public section

/-! Zero extension on the unit cube, proved by an asymmetric face-patch fractional
Hardy estimate. H1_0 approximation supplies weighted finiteness for absorption;
Tonelli and a truncated radial kernel bound the two exterior interaction terms.
The principal below is unchanged from the author's declaration. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem classical_unit_cube_fractional_zero_extension (d : ℕ) (hd : 2 ≤ d)
    (s : Set.Ioo (0 : ℝ) 1) (hs : (1 / 2 : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
        ∃ V : SpatialCoordinates d → ℝ,
          (((v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 :
              SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
              Set (SpatialCoordinates d))] V) ∧
          (∀ x, x ∉ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) → V x = 0) ∧
          globalFractionalSqNorm s V ≤ ENNReal.ofReal
            (C * cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) := by
  exact SubdiffusiveProcess.exists_unit_cube_fractional_zero_extension d hd s hs

end SubdiffusiveProcess.Paper
