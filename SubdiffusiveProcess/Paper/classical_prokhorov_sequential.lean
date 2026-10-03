module

public import SubdiffusiveProcess.Probability.ProkhorovTight
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.MetricSpace.Polish

@[expose] public section

/-! Sequential Prokhorov compactness for probability measures on a Polish space.
The proof uses compact-space RMK and Banach–Alaoglu, a countable-cube embedding,
and tightness with Portmanteau to recover the limit on the source space. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory
open scoped Topology
namespace Paper

theorem classical_prokhorov_sequential
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : ℕ → ProbabilityMeasure X)
    (htight : IsTightMeasureSet (Set.range (fun n => (mu n : Measure X)))) :
    ∃ (seq : ℕ → ℕ) (nu : ProbabilityMeasure X), StrictMono seq ∧
      Tendsto (fun n => mu (seq n)) atTop (𝓝 nu) := by
  exact SubdiffusiveProcess.Probability.prokhorov_sequential mu htight

end Paper
