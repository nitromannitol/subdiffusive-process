module

public import SubdiffusiveProcess.Processes.PathProductTests
public import SubdiffusiveProcess.Processes.PathTestInversion
public import SubdiffusiveProcess.Processes.PathTimeExtension

@[expose] public section

open MeasureTheory Set
open scoped NNReal BigOperators BoundedContinuousFunction

namespace SubdiffusiveProcess

/-- Integrated tests at positive integer rates determine a continuous-path law. -/
theorem continuousPath_eq_of_integrated_tests
    {d : ℕ}
    [MeasurableSpace C(ℝ≥0, SpatialCoordinates d)]
    [BorelSpace C(ℝ≥0, SpatialCoordinates d)]
    (A : Set (SpatialCoordinates d →ᵇ ℝ))
    (h1 : (1 : SpatialCoordinates d →ᵇ ℝ) ∈ A)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A)
    (hsep : ∀ x y : SpatialCoordinates d, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (P Q : ProbabilityMeasure C(ℝ≥0, SpatialCoordinates d))
    (heq : ∀ (k : ℕ) (f : Fin k → (SpatialCoordinates d →ᵇ ℝ)),
      (∀ i, f i ∈ A) → ∀ m : Fin k → ℕ,
      (∫ z : C(ℝ≥0, SpatialCoordinates d),
        (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
          Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * s i)) *
            ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
        ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
      ∫ z : C(ℝ≥0, SpatialCoordinates d),
        (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
          Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * s i)) *
            ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
        ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d))) :
    P = Q := by
  apply continuousPath_eq_of_product_expectations A h1 hmul hsep P Q
  intro k t f hf
  apply path_product_expectation_eq_of_positive_increments A P Q ?_ t f hf
  intro g hg s hs
  exact path_product_expectation_eq_of_integrated_tests P Q g (heq k g hg) s hs

end SubdiffusiveProcess
