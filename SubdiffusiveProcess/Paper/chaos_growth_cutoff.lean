import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.ChaosCutoff
import SubdiffusiveProcess.Main.ConditionalFineFiltration
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Probability.CubeMassMartingale
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Probability.Martingale.Basic
import SubdiffusiveProcess.Lane1.GrowthCutoff
import SubdiffusiveProcess.Paper.doob_lp_maximal
import SubdiffusiveProcess.Paper.lem_chaos_moments

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem chaos_growth_cutoff
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo 0 1)
    (p : ℕ) (hp : (d : ℝ) < p * epsilon) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Kmu : BilateralField d → ℝ,
            MemLp Kmu p (chaosSampleLaw M).toMeasure ∧
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              0 ≤ Kmu omega ∧
              ∀ N x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                weightedChaosCutoff M H N omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) :=
  SubdiffusiveProcess.chaos_growth_cutoff hd epsilon hepsilon p hp

end Paper
