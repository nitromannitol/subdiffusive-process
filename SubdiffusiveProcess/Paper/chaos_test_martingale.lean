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
import SubdiffusiveProcess.Paper.lem_chaos_moments
import SubdiffusiveProcess.Lane1.TestFunctionMartingale
import Mathlib.Topology.ContinuousMap.CompactlySupported

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem chaos_test_martingale
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (f : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    Martingale (fun N omega => ∫ x, f x ∂(weightedChaosCutoff M H N omega))
        (conditionalFineFiltration H hH.1) (chaosSampleLaw M).toMeasure ∧
      ∀ (N : ℕ) (omega : BilateralField d),
        0 ≤ ∫ x, f x ∂(weightedChaosCutoff M H N omega) :=
  SubdiffusiveProcess.chaos_test_martingale hd M H hH f hf

end Paper
