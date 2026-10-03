module

public import SubdiffusiveProcess.Paper.in_killed_energy
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.in_cube_notation
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.GradientRange

@[expose] public section

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def in_dirichlet_response {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d)
    (hH : ∀ x, H omega x = ∑' j : Nat, (omega ((j : Int) + 1) x - omega ((j : Int) + 1) 0))
    (N : Nat) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr)) : ℝ :=
  dirichletResponse (killedResponseSpace hP)
    (Lane4.cutoffPositiveCoefficient M H omega N z hr) b

end Paper
