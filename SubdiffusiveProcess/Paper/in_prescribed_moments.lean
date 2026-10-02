import SubdiffusiveProcess.Main.ChaosSampleLaw
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal

namespace Paper



def in_prescribed_moments {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (orders : Finset ℝ)
    (K : (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) → Nat → BilateralField d → ℝ) : Prop :=
  (∀ p ∈ orders, 0 < p) ∧
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
        ∀ p ∈ orders, ∃ C : ℝ, 0 ≤ C ∧
          ∀ N : Nat,
            eLpNorm (K M N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal C

end Paper
