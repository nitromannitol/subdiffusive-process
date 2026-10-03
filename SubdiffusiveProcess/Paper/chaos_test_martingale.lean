module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Probability.Martingale.Basic
public import SubdiffusiveProcess.Paper.lem_chaos_moments
public import SubdiffusiveProcess.Lane1.TestFunctionMartingale
public import Mathlib.Topology.ContinuousMap.CompactlySupported

@[expose] public section

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
