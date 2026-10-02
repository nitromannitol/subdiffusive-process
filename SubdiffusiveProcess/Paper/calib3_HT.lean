import Mathlib
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Paper.prop_growth_large_root

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal
noncomputable section
namespace Paper

/-- The "top-block removal" potential `HT_j(ω) = -∑_{i<j} ω(-i)`: the negative of the `j` coarsest layers of the
cutoff coefficient (Stage 3 of the calibration).  Under the scale shift `S_j ω (m)(y) = ω (m + j) (3^j y)` the infrared-free
coefficient `A^0_N` of a cube of side `3^j` becomes, up to a deterministic constant, the level-`N+j` coefficient of `S_j ω`
with potential `HT_j` (paper: rescaling of the proof of `mfd:prop-growth`, lines 598-617, for `H = 0`). -/
def calib3_HT (d : ℕ) (j : ℕ) : BilateralField d → C(SpatialCoordinates d, ℝ) :=
  fun om => -(∑ i ∈ Finset.range j, om (-(Int.ofNat i)))

end Paper
