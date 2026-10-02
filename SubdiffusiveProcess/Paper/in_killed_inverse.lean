import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Sobolev.GradientRange
import SubdiffusiveProcess.Paper.in_killed_energy
import SubdiffusiveProcess.Paper.in_normalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess

open scoped ENNReal NNReal

noncomputable section
namespace Paper



def in_killed_inverse {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H) (omega : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (f : DomainL2 (centeredCube z r hr)) :
    killedSobolevGraph (centeredCube z r hr) :=
  responseSolution (killedResponseSpace hP)
    (Lane4.cutoffPositiveCoefficient M H omega N z hr)
    ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)

end Paper
