import Mathlib
/-!

An almost-everywhere predicate can be made pointwise outside a measurable bad event by adjoining a measurable null hull. The probability bound is preserved.
-/

set_option autoImplicit false
open MeasureTheory Filter
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Remove one null exception before all downstream universal solution quantifiers. -/
theorem goodCube_exists_measurable_bad_union_null
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (Bad : Set Omega) (hBad : MeasurableSet Bad)
    (P : Omega → Prop) (hP : ∀ᵐ omega ∂mu, P omega) :
    ∃ B : Set Omega, MeasurableSet B ∧ mu B ≤ mu Bad ∧
      ∀ omega, omega ∉ B → omega ∉ Bad ∧ P omega := by
  have hnull : mu {x | ¬ P x} = 0 := ae_iff.1 hP
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null hnull
  refine ⟨Bad ∪ N, hBad.union hNmeas, ?_, ?_⟩
  · have h1 : mu (Bad ∪ N) ≤ mu Bad + mu N := measure_union_le Bad N
    rw [hNnull] at h1
    simpa using h1
  · intro omega homega
    have hnotN : omega ∉ N := fun h => homega (Or.inr h)
    have hnotBad : omega ∉ Bad := fun h => homega (Or.inl h)
    have hPomega : P omega := by
      by_contra hcon
      exact hnotN (hNsub (fun h => hcon h))
    exact ⟨hnotBad, hPomega⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
