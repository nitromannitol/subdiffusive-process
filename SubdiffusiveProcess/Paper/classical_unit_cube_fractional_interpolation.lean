import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Analysis.CubeFractionalInterpolation

/-! Fractional interpolation on the unit cube, proved by a near/far split of the
Gagliardo integral and optimization of the splitting scale. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

theorem classical_unit_cube_fractional_interpolation (d : ℕ) (hd : 2 ≤ d)
    (s t : Set.Ioo (0 : ℝ) 1) (hts : (t : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => v) < ⊤ →
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => v) < ⊤ ∧
      Real.sqrt (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos t v) ≤
        C * (‖v‖ / Real.sqrt (volume.real
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))) ^
            (1 - (t : ℝ) / s) *
          Real.sqrt (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s v) ^ ((t : ℝ) / s) := by
  exact exists_unit_cube_fractional_interpolation d hd s t hts

end Paper
