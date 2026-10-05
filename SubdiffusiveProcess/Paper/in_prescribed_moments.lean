module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper

/--
- orders is a finite list of positive prescribed moment orders, fixed before delta0.
- The threshold is outside the model and cutoff quantifiers; it can depend on d, the fixed list, and the chosen family with its fixed auxiliary parameters.
- Each finite moment bound is uniform in N.
- This convention does not claim a pathwise supremum bound; those are established in the later pathwise subsection.
-/
def in_prescribed_moments {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (orders : Finset ℝ)
    (K : (M : _root_.SubdiffusiveProcess.Model.GMCModel d) → Nat → BilateralField d → ℝ) : Prop :=
  (∀ p ∈ orders, 0 < p) ∧
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
        ∀ p ∈ orders, ∃ C : ℝ, 0 ≤ C ∧
          ∀ N : Nat,
            eLpNorm (K M N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal C

end SubdiffusiveProcess.Paper
