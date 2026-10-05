module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Analysis.CubeFractionalExtension

@[expose] public section

/-! Fractional extension from the unit cube, proved by even reflection on the
tripled cube and multiplication by a Lipschitz cutoff. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem classical_unit_cube_fractional_extension (d : ℕ) (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => v) < ⊤ →
      ∃ V : SpatialCoordinates d → ℝ,
        ((v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))] V) ∧
        globalFractionalSqNorm s V ≤
          ENNReal.ofReal (C * cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s v) := by
  exact SubdiffusiveProcess.exists_unit_cube_fractional_extension d hd s

end SubdiffusiveProcess.Paper
