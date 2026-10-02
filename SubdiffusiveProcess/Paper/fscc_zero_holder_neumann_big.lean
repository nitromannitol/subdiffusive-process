import SubdiffusiveProcess.Paper.fscc_holder_predicates
import SubdiffusiveProcess.Paper.fscc_zero_holder_neumann_big_transport
import SubdiffusiveProcess.Paper.neumann_ht_unit_holder
import SubdiffusiveProcess.Paper.cor_neumann_source
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.MeanZero
import SubdiffusiveProcess.Probability.GMCFieldLaws
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The mean-zero Neumann Hölder branch for the infrared-free coefficient, at every exponent `α ∈ (0,1)`

Paper `mfd:lem-finite-source-comparison` (last paragraph of its proof), Neumann half, on every
triadic root cube `Q(z, 3^j)` and every cutoff `J ≥ max 0 (-j)`.  (The finitely many cutoffs
`J < -j` of a small cube are not covered here.)  The Hölder exponent is a parameter.

The statement is split by the sign of `j`: `fscc_zero_holder_neumann_small` (`j ≤ 0`, cubes of side
at most `1`: the T-transport lands in the truncation class `H_L`, `L ≥ 0`, of the unit cube) and
`fscc_zero_holder_neumann_big` (`j > 0`, cubes larger than the field's top scale: the transport lands
in the negative class `H_{-j}`, the `j` coarsest UV layers deleted); `fscc_zero_holder_neumann`
combines them by cases with the smaller of the two thresholds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology Metric ProbabilityTheory
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper

/-- **The mean-zero Neumann Hölder branch for the infrared-free coefficient, cubes of side `3^j > 1`
(`j > 0`), every cutoff `J ≥ 0`, every exponent `α ∈ (0,1)`.**  Same conclusion as
`fscc_zero_holder_neumann_small`; the threshold `delta0` is independent of `j`. -/
theorem fscc_zero_holder_neumann_big
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg),
        model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (j : ℤ) (r : ℝ) (hr : 0 < r), r = (3 : ℝ) ^ j → 0 < j →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbank : ℝ),
        (∀ J, MemLp (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
        (∀ J, eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal Cbank) ∧
        ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, -j ≤ (J : ℤ) →
          aux_fscc_holder_predicates_holNeu d z r hr
            (cutoffPositiveCoefficient model
              (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega J z hr)
            alpha (K J omega) := by
  exact fscc_zero_holder_neumann_big_transport d hd E alpha ha0 ha1
    (neumann_ht_unit_holder d hd E P X W D Cp alpha ha0 ha1)

end Paper
