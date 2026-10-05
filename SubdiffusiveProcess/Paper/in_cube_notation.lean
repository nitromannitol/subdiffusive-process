module

public import SubdiffusiveProcess.Geometry.Cube

@[expose] public section

open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



abbrev in_cube_notation {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    TopologicalSpace.Opens (SpatialCoordinates d) :=
  centeredCube z r hr

end SubdiffusiveProcess.Paper
