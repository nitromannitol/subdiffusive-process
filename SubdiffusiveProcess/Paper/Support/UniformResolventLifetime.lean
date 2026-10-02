import SubdiffusiveProcess.Paper.Support.CutoffLifetimeInput

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
noncomputable section
namespace Paper



theorem aux_mfd_prop_uniform_resolvent_lifetime {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN) :
    ∃ L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d),
      (∀ N omega x, Measure.map LifetimePath.ofContinuousPath
        (KN N (omega, x)) = L N omega x) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        LocalDiffusionData (cutoffCoefficient M H omega N)
          (cutoffSpeedDensity M H omega N) (L N omega)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N, StrongMarkov (L N omega)) := by
  exact cutoff_lifetime_package M H KN
    (SubdiffusiveProcess.Examples.cutoff_lifetime_input hd M H hH PN KN hKN hin)

end Paper
