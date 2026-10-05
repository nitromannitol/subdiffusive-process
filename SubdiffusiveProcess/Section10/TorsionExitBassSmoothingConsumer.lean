module

public import SubdiffusiveProcess.Section10.TorsionExitBassStartConsumer
public import SubdiffusiveProcess.Section10.ReversibleKilledSmoothing

@[expose] public section

/-! Consumption of the PROVED arbitrary-open weighted smoothing supplier.
The sole remaining completing target is the local whole-space L1 estimate;
RRK, dimension two, every-start continuity and actual early exit are proved. -/

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Actual reversible density assembly with the independent smoothing and
starting-point continuity proofs consumed. Only the rough local estimate is
still an explicit completing target, not a classical leaf or source premise. -/
theorem smoothReversibleKilledDensitySupplier_of_localL1Estimate
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (happrox : ReversibleFellerLocalL1ApproximationSupplier) :
    SmoothReversibleKilledDensitySupplier :=
  smoothReversibleKilledDensitySupplier_of_bassEstimates
    hFOT reversibleKilledSmoothingSupplier happrox

end SubdiffusiveProcess.Section10
