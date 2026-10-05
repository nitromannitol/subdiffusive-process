module

public import SubdiffusiveProcess.Paper.fscc_holder_predicates
public import SubdiffusiveProcess.Paper.fscc_zero_holder_neumann_small
public import SubdiffusiveProcess.Paper.fscc_zero_holder_neumann_big
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.MeanZero
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
# The mean-zero Neumann Hölder branch for the infrared-free coefficient, at every exponent `α ∈ (0,1)`

Paper `mfd:lem-finite-source-comparison` (last paragraph of its proof), Neumann half, on every
triadic root cube `Q(z, 3^j)` and every cutoff `J ≥ max 0 (-j)`.  (The finitely many cutoffs
`J < -j` of a small cube are not covered here.)  The Hölder exponent is a parameter.

The statement is split by the sign of `j`: `fscc_zero_holder_neumann_small` (`j ≤ 0`, cubes of side
at most `1`: the T-transport lies in the truncation class `H_L`, `L ≥ 0`, of the unit cube) and
`fscc_zero_holder_neumann_big` (`j > 0`, cubes larger than the field's top scale: the transport lies
in the negative class `H_{-j}`, the `j` coarsest UV layers deleted); `fscc_zero_holder_neumann`
combines them by cases with the smaller of the two thresholds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology Metric ProbabilityTheory
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **The mean-zero Neumann Hölder branch for the infrared-free coefficient, every exponent
`α ∈ (0,1)`, every triadic root `r = 3^j`, every cutoff `J ≥ -j`** (paper
`mfd:lem-finite-source-comparison`, last paragraph of the proof): the small and the big roots
combined.  One threshold `delta0` for the exponent, before the model, the root and the cutoff. -/
theorem fscc_zero_holder_neumann
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg),
        model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (j : ℤ) (r : ℝ) (hr : 0 < r), r = (3 : ℝ) ^ j →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbank : ℝ),
        (∀ J, MemLp (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
        (∀ J, eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal Cbank) ∧
        ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, -j ≤ (J : ℤ) →
          aux_fscc_holder_predicates_holNeu d z r hr
            (cutoffPositiveCoefficient model
              (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega J z hr)
            alpha (K J omega) := by
  obtain ⟨d1, hd1, h1⟩ := fscc_zero_holder_neumann_small d hd E P X W Cp Sf D alpha ha0 ha1
  obtain ⟨d2, hd2, h2⟩ := fscc_zero_holder_neumann_big d hd E P X W Cp Sf D alpha ha0 ha1
  refine ⟨min d1 d2, lt_min hd1 hd2, ?_⟩
  intro model Rm Sreg It hδ z j r hr hr3
  rcases le_or_gt j 0 with hj | hj
  · exact h1 model Rm Sreg It (hδ.trans (min_le_left _ _)) z j r hr hr3 hj
  · exact h2 model Rm Sreg It (hδ.trans (min_le_right _ _)) z j r hr hr3 hj

end SubdiffusiveProcess.Paper
