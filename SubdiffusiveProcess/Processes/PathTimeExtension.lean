import SubdiffusiveProcess.Analysis.PositiveIncrements
import SubdiffusiveProcess.Processes.PathTests
import Mathlib.Data.Fin.Tuple.Sort

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators BoundedContinuousFunction

namespace SubdiffusiveProcess

/-- Positive-increment product expectations determine all observation-time products within the same test family. -/
theorem path_product_expectation_eq_of_positive_increments
    {d k : ℕ}
    [MeasurableSpace C(ℝ≥0, SpatialCoordinates d)]
    [BorelSpace C(ℝ≥0, SpatialCoordinates d)]
    (A : Set (SpatialCoordinates d →ᵇ ℝ))
    (P Q : ProbabilityMeasure C(ℝ≥0, SpatialCoordinates d))
    (heq : ∀ f : Fin k → (SpatialCoordinates d →ᵇ ℝ), (∀ i, f i ∈ A) →
      ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      (∫ z : C(ℝ≥0, SpatialCoordinates d),
        ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))
        ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
      ∫ z : C(ℝ≥0, SpatialCoordinates d),
        ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))
        ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d)))
    (t : Fin k → ℝ≥0) (f : Fin k → (SpatialCoordinates d →ᵇ ℝ))
    (hf : ∀ i, f i ∈ A) :
    (∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, f i (z (t i))
      ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
    ∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, f i (z (t i))
      ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d)) := by
  classical
  let σ : Equiv.Perm (Fin k) := Tuple.sort t
  let g : Fin k → (SpatialCoordinates d →ᵇ ℝ) := fun i => f (σ i)
  let u : Fin k → ℝ≥0 := t ∘ σ
  have hu : Monotone u := Tuple.monotone_sort t
  obtain ⟨s, hs_pos, hs_lim⟩ := exists_positive_increments_tendsto u hu
  let v : ℕ → Fin k → ℝ≥0 := fun n i =>
    Real.toNNReal (∑ j ∈ Finset.Iic i, s n j)
  have hseq : ∀ n,
      (∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, g i (z (v n i))
        ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
      ∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, g i (z (v n i))
        ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d)) := by
    intro n
    exact heq g (fun i => hf (σ i)) (s n) (hs_pos n)
  have hP := (continuous_path_product_expectation P g).continuousAt.tendsto.comp hs_lim
  have hQ := (continuous_path_product_expectation Q g).continuousAt.tendsto.comp hs_lim
  have hsorted :
      (∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, g i (z (u i))
        ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
      ∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, g i (z (u i))
        ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d)) := by
    apply tendsto_nhds_unique hP
    convert hQ using 1
    ext n
    exact hseq n
  calc
    (∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, f i (z (t i))
        ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
        ∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, g i (z (u i))
          ∂(P : Measure C(ℝ≥0, SpatialCoordinates d)) := by
            congr 1
            funext z
            exact (Equiv.prod_comp σ (fun i => f i (z (t i)))).symm
    _ = ∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, g i (z (u i))
          ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d)) := hsorted
    _ = ∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, f i (z (t i))
          ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d)) := by
            congr 1
            funext z
            exact Equiv.prod_comp σ (fun i => f i (z (t i)))

end SubdiffusiveProcess
