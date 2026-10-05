module

public import SubdiffusiveProcess.Paper.in_killed_inverse
public import SubdiffusiveProcess.Paper.in_killed_energy
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Sobolev.GradientRange
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/--
- The space is exactly the killed Sobolev graph on the cube, via S = killedResponseSpace hP.
- hP is the ordinary cube Poincare input implicit in the energy-inner-product construction in in_killed_inverse (paper label `eq:mfd-quadratic-response`).
- a is the concrete A_N of in_killed_energy; L is exactly the Lebesgue load of f.
- The weak solution is responseSolution; its construction is the inverse in in_killed_inverse.
- The supremum formula is an IsGreatest conclusion, and attainment is asserted specifically at that weak solution.
-/
theorem quadratic_inverse_response
    {d : Nat}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
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
    (_hS : S = killedResponseSpace hP)
    (a : PositiveCoefficient (centeredCube z r hr))
    (_ha : a = _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
    (L : S.space →L[ℝ] ℝ)
    (_hL : L = (sobolevVolumeLoad f).comp S.space.subtypeL) :
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


end SubdiffusiveProcess.Paper
