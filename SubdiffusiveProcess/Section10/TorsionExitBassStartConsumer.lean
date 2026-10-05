module

public import SubdiffusiveProcess.Section10.TorsionExitBassConsumer
public import SubdiffusiveProcess.Section10.FellerKilledStartContinuity

@[expose] public section

/-! Consumption of the proved original-law continuity supplier.
Only the two independent weighted estimates remain completing inputs; actual
early exit and every-start law promotion are discharged. -/

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The completed original-law continuity proof fills the exact RRK killed
density field for the actual reversible weak-resolvent/Feller family. -/
theorem smoothReversibleKilledDensitySupplier_of_bassEstimates
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (hsmooth : ReversibleKilledSmoothingSupplier)
    (happrox : ReversibleFellerLocalL1ApproximationSupplier) :
    SmoothReversibleKilledDensitySupplier :=
  smoothReversibleKilledDensitySupplier_of_bassSuppliers
    hFOT hsmooth happrox fellerKilledStartContinuitySupplier

end SubdiffusiveProcess.Section10
