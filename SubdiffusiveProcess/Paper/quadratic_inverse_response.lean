import SubdiffusiveProcess.Paper.in_killed_inverse
import SubdiffusiveProcess.Paper.in_killed_energy
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Sobolev.GradientRange
import SubdiffusiveProcess.Lane4.Carriers

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal NNReal

namespace Paper



theorem quadratic_inverse_response
    {d : Nat}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d)
    (N : Nat)
    (z : SpatialCoordinates d)
    (r : ℝ)
    (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (f : DomainL2 (centeredCube z r hr))
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S = killedResponseSpace hP)
    (a : PositiveCoefficient (centeredCube z r hr))
    (ha : a = Lane4.cutoffPositiveCoefficient M H omega N z hr)
    (L : S.space →L[ℝ] ℝ)
    (hL : L = (sobolevVolumeLoad f).comp S.space.subtypeL) :
    IsGreatest (Set.range (fun v : S.space => 2 * L v - responseForm S a v v))
      (L (responseSolution S a L)) ∧
    2 * L (responseSolution S a L) -
        responseForm S a (responseSolution S a L) (responseSolution S a L) =
      L (responseSolution S a L) := by
  constructor
  · rw [← inverseResponse_eq_load S a L]
    exact inverseResponse_isGreatest S a L
  · rw [responseSolution_spec S a L (responseSolution S a L)]
    ring


end Paper
