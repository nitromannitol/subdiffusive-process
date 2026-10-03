module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Failure probabilities are invariant under the paper's shifted field. -/
theorem aux_lem_as_coarse_shallow_grid_shifted_bank_tail {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (k : ℕ) (w : SpatialCoordinates d)
    (Z : BilateralField d → ℝ) (t : ℝ)
    (hZ : Measurable Z) :
    (chaosSampleLaw model).toMeasure
      {omega | t ≤ |Z (aux_lem_as_coarse_shallow_grid_scaleShift k w omega)|} =
    (chaosSampleLaw model).toMeasure {omega | t ≤ |Z omega|} := by
  set P := (chaosSampleLaw model).toMeasure
  set f := aux_lem_as_coarse_shallow_grid_scaleShift k w
  have hpreserving : MeasurePreserving f P P :=
    lem_as_coarse_shallow_grid_scale_shift model k w
  have hmeas : MeasurableSet {ω | t ≤ |Z ω|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp hZ)
  calc
    P {ω | t ≤ |Z (f ω)|} = P (f ⁻¹' {ω | t ≤ |Z ω|}) := rfl
    _ = P {ω | t ≤ |Z ω|} := hpreserving.measure_preimage hmeas.nullMeasurableSet

/-- A unit-cube response moment bound transfers to each shifted grid cell under
the same chaos sample law and with the same constant. -/
theorem lem_as_coarse_shallow_grid_shifted_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (k : ℕ) (w : SpatialCoordinates d)
    (Z : BilateralField d → ℝ) (p C : ℝ≥0∞)
    (hZ : AEStronglyMeasurable Z (chaosSampleLaw model).toMeasure)
    (hbound : eLpNorm Z p (chaosSampleLaw model).toMeasure ≤ C) :
    eLpNorm (fun omega => Z (aux_lem_as_coarse_shallow_grid_scaleShift k w omega))
      p (chaosSampleLaw model).toMeasure ≤ C := by
  set P := (chaosSampleLaw model).toMeasure
  have hpreserving : MeasurePreserving (aux_lem_as_coarse_shallow_grid_scaleShift k w) P P :=
    lem_as_coarse_shallow_grid_scale_shift model k w
  have heq : eLpNorm (Z ∘ (aux_lem_as_coarse_shallow_grid_scaleShift k w)) p P =
      eLpNorm Z p P :=
    eLpNorm_comp_measurePreserving hZ hpreserving
  calc
    eLpNorm (fun omega => Z (aux_lem_as_coarse_shallow_grid_scaleShift k w omega)) p P =
        eLpNorm (Z ∘ (aux_lem_as_coarse_shallow_grid_scaleShift k w)) p P := rfl
    _ = eLpNorm Z p P := heq
    _ ≤ C := hbound

end Paper


