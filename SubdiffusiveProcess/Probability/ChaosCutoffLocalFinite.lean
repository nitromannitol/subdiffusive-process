module

public import SubdiffusiveProcess.Main.ChaosCutoff

@[expose] public section

open MeasureTheory
noncomputable section
namespace SubdiffusiveProcess

theorem chaosCutoff_isLocallyFinite
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (omega : BilateralField d) :
    IsLocallyFiniteMeasure (chaosCutoff M N omega) := by
  unfold chaosCutoff
  apply IsLocallyFiniteMeasure.withDensity_ofReal
  unfold fineDensity finePotential
  apply Real.continuous_exp.comp
  apply Continuous.sub
  · fun_prop
  · fun_prop

end SubdiffusiveProcess
