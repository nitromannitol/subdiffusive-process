module

public import SubdiffusiveProcess.Processes.PathLaw
public import SubdiffusiveProcess.Probability.ProductTests

@[expose] public section

open MeasureTheory Set
open scoped NNReal BigOperators BoundedContinuousFunction

namespace SubdiffusiveProcess

/-- Products of a unital separating family determine continuous-path laws at all nonnegative times. -/
theorem continuousPath_eq_of_product_expectations
    {d : ℕ}
    [MeasurableSpace C(ℝ≥0, SpatialCoordinates d)]
    [BorelSpace C(ℝ≥0, SpatialCoordinates d)]
    (A : Set (SpatialCoordinates d →ᵇ ℝ))
    (h1 : (1 : SpatialCoordinates d →ᵇ ℝ) ∈ A)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A)
    (hsep : ∀ x y : SpatialCoordinates d, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (P Q : ProbabilityMeasure C(ℝ≥0, SpatialCoordinates d))
    (heq : ∀ (k : ℕ) (t : Fin k → ℝ≥0)
      (f : Fin k → (SpatialCoordinates d →ᵇ ℝ)), (∀ i, f i ∈ A) →
      (∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, f i (z (t i))
        ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
      ∫ z : C(ℝ≥0, SpatialCoordinates d), ∏ i : Fin k, f i (z (t i))
        ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d))) :
    P = Q := by
  apply continuousPath_probabilityMeasure_ext P Q
  intro I
  let e : Fin I.card ≃ I :=
    (finCongr (Fintype.card_coe I).symm).trans (Fintype.equivFin I).symm
  let obs : C(ℝ≥0, SpatialCoordinates d) → (Fin I.card → SpatialCoordinates d) :=
    fun z i => z (e i)
  have hobs : Measurable obs := by
    apply measurable_pi_lambda
    intro i
    change Measurable (fun z : C(ℝ≥0, SpatialCoordinates d) => z (e i : ℝ≥0))
    exact (continuous_eval_const (e i : ℝ≥0)).measurable
  have hfin : Measure.map obs (P : Measure C(ℝ≥0, SpatialCoordinates d)) =
      Measure.map obs (Q : Measure C(ℝ≥0, SpatialCoordinates d)) := by
    apply measure_eq_of_separating_product_integrals A h1 hmul hsep
    intro f hf
    have hg : Continuous (fun x : Fin I.card → SpatialCoordinates d =>
        ∏ i : Fin I.card, f i (x i)) := by
      fun_prop
    rw [integral_map hobs.aemeasurable hg.aestronglyMeasurable,
      integral_map hobs.aemeasurable hg.aestronglyMeasurable]
    exact heq I.card (fun i => e i) f hf
  let reindex : (Fin I.card → SpatialCoordinates d) → (I → SpatialCoordinates d) :=
    fun x j => x (e.symm j)
  have hreindex : Measurable reindex :=
    Measurable.of_eval fun j => measurable_pi_apply (e.symm j)
  calc
    Measure.map (fun z : C(ℝ≥0, SpatialCoordinates d) => fun t : I => z t)
        (P : Measure C(ℝ≥0, SpatialCoordinates d)) =
        Measure.map reindex (Measure.map obs (P : Measure C(ℝ≥0, SpatialCoordinates d))) := by
          rw [Measure.map_map hreindex hobs]
          congr
          funext z t
          simp [reindex, obs]
    _ = Measure.map reindex (Measure.map obs (Q : Measure C(ℝ≥0, SpatialCoordinates d))) := by
      rw [hfin]
    _ = Measure.map (fun z : C(ℝ≥0, SpatialCoordinates d) => fun t : I => z t)
        (Q : Measure C(ℝ≥0, SpatialCoordinates d)) := by
          rw [Measure.map_map hreindex hobs]
          congr
          funext z t
          simp [reindex, obs]

end SubdiffusiveProcess
