module

public import SubdiffusiveProcess.Section10.TorsionExitDensityPhysical
public import SubdiffusiveProcess.Section10.TorsionExitBassActual
public import SubdiffusiveProcess.Paper.inputs_classical_fot_part_process

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- The exact reversible killed-density continuity step for every original
interior start, supplied by the completed weighted RRK/Feller proof. -/
theorem lim_killed_density_continuity :
    SubdiffusiveProcess.Section10.SmoothReversibleKilledDensitySupplier := by
  exact SubdiffusiveProcess.Section10.smoothReversibleKilledDensitySupplier
    (show SubdiffusiveProcess.E7.FOTPartProcess from inputs_classical_fot_part_process)

end SubdiffusiveProcess.Paper
