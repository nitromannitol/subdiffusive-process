module

public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



def neumann_load {d : ℕ} (z : SpatialCoordinates d) (hr : (0 : ℝ) < 1)
    (p : SpatialCoordinates d) (v : weakSobolevGraph (centeredCube z 1 hr)) : ℝ :=
  ∑ i : Fin d, p i *
    ∫ x in (centeredCube z 1 hr : Set (SpatialCoordinates d)),
      (sobolevGradient (v : SobolevData (centeredCube z 1 hr)) i) x

end SubdiffusiveProcess.Paper
