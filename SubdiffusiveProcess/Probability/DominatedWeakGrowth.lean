module

public import SubdiffusiveProcess.Probability.FiniteMeasureGrowth

@[expose] public section

/-! Bounds for open sets pass to measures dominated by a weak limit.
Only eventual bounds for each test set are required; no uniform microscopic radius is assumed. -/
open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace SubdiffusiveProcess

/-- A measure dominated by a weak limit inherits every eventual bound on an open test set. -/
theorem measure_le_of_dominated_weak_limit_eventually
    {X : Type*} [Nonempty X] [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {muN : ℕ → FiniteMeasure X} {mu : FiniteMeasure X} (nu : Measure X)
    (hconv : Tendsto muN atTop (𝓝 mu))
    (hdom : ∀ B : Set X, MeasurableSet B → nu B ≤ (mu : Measure X) B)
    {U : Set X} (hU : IsOpen U) (b : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, (muN n : Measure X) U ≤ b) : nu U ≤ b := by
  exact (hdom U hU.measurableSet).trans
    ((finiteMeasure_le_liminf_open hconv hU).trans
      ((liminf_le_liminf hbound).trans_eq (liminf_const b)))

end SubdiffusiveProcess
