module

public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.in_killed_energy

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal BigOperators

noncomputable section
namespace Paper



def in_energy_measure {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (u : weakSobolevGraph (centeredCube z r hr)) :
    Measure (SpatialCoordinates d) :=
  (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
    (fun x => ENNReal.ofReal (cutoffCoefficient M H omega N x *
      (∑ i : Fin d, ((((u : SobolevData (centeredCube z r hr)).2 i) x) ^ 2))))

end Paper
