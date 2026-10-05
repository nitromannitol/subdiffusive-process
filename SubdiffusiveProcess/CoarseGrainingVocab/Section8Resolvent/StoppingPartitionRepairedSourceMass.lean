module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedSource
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderL2Data

@[expose] public section

/-!
# Source-cell mass bound from the global L2 contraction

The P-201 whole-space construction supplies `∫u² ≤ ∫f²`.  Since the
integrand is nonnegative, restriction to any repaired stopping cell gives the
source-cell mass premise of the exterior-row consumer.

## Source

* `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.Frozen.Section8

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- The squared mass on any repaired stopping cell is bounded by the global
squared mass of the whole-space solution. -/
theorem setIntegral_sq_refinedStoppingCell_le_integral_sq
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (q : RefinedStoppingCell failure omega base) :
    ∫ x in translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q),
        u.toFun x ^ 2 ∂volume ≤
      ∫ x, u.toFun x ^ 2 ∂volume := by
  apply setIntegral_le_integral u.memL2_toFun.integrable_sq
  exact Filter.Eventually.of_forall fun x ↦ sq_nonneg (u.toFun x)

/-- The global L2 contraction supplied by P-201 discharges the source-cell
mass premise in the exact graph-distance shape used by the exterior row. -/
theorem repairedStopping_sourceMass_le_of_l2_contraction
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) :
    ∀ q, stoppingGraphDistance repairedStoppingGraph source hsource q = 0 →
      ∫ x in translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q),
          u.toFun x ^ 2 ∂volume ≤
        ∫ x, f x ^ 2 ∂volume := by
  intro q _
  exact (setIntegral_sq_refinedStoppingCell_le_integral_sq u q).trans hL2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
