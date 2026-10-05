module

public import SubdiffusiveProcess.MultiplicativeChaos.MeanPositiveTest

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The mean mass of a cube survives in the limit (the first
input of the full-support argument; the second is the zero-one law).

The cube masses of the cutoff chaos are a nonnegative martingale, so their
mean does not move, and they are bounded in `L^p` with `p >= 2` by
`\noderef{lem_chaos_moments}`.  A family with constant positive mean, bounded
in `L^p`, cannot converge almost surely to zero: truncating at height `c`
costs at most `E[X^p]/c^(p-1)`, so the truncated means stay above half the
mean for `c` large, and dominated convergence carries that to the limit.

The argument is run on a test function supported under the cube rather than on
the cube itself, because that is what vague convergence delivers: the test
integral is dominated by the cube mass, which carries the `L^p` bound across,
and no identification of the limit of the cube masses is needed. -/
theorem chaos_mean_positive
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (mu : BilateralField d → Measure (SpatialCoordinates d))
    (hmumble : Measurable mu)
    (hlocfin : ∀ omega, IsLocallyFiniteMeasure (mu omega))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (p : ℕ) (hp : 2 ≤ p) (Cmom : ℝ)
    (hintp : ∀ N : ℕ, Integrable (fun omega =>
      (((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) ^ p)
      (chaosSampleLaw M).toMeasure)
    (hmom : ∀ N : ℕ, ∫ omega,
      (((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) ^ p
      ∂(chaosSampleLaw M).toMeasure ≤ Cmom)
    (hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally
        (fun N => weightedChaosCutoff M H N omega) (mu omega)) :
    0 < ∫⁻ omega, mu omega (centeredCube z r hr : Set (SpatialCoordinates d))
      ∂(chaosSampleLaw M).toMeasure :=
  SubdiffusiveProcess.chaos_mean_positive_of_vague hd M H hH mu hmumble hlocfin
    z r hr p hp Cmom hintp hmom hconv

end SubdiffusiveProcess.Paper
