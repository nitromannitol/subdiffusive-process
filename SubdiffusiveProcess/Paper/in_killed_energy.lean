module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.in_cube_notation
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Main.InfraredCharacterization

@[expose] public section

open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def in_killed_energy {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    killedSobolevGraph (centeredCube z r hr) →
      killedSobolevGraph (centeredCube z r hr) → ℝ :=
  fun u v =>
    sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
      (u : SobolevData (centeredCube z r hr))
      (v : SobolevData (centeredCube z r hr))

end Paper
