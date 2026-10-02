import Mathlib.MeasureTheory.Measure.Typeclasses.Probability




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The cutoff index of Theorem C is countable, so intersecting over it is
legitimate. -/
example : Countable (WithTop ℕ) := inferInstance

/-- A countable intersection of probability-one events has probability one. -/
theorem measure_iInter_eq_one {ι : Type*} [Countable ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {E : ι → Set Ω}
    (hmeas : ∀ i, MeasurableSet (E i)) (hfull : ∀ i, μ (E i) = 1) :
    μ (⋂ i, E i) = 1 := by
  have hcompl : ∀ i, μ (E i)ᶜ = 0 := fun i ↦
    (prob_compl_eq_zero_iff (hmeas i)).2 (hfull i)
  have hnull : μ (⋂ i, E i)ᶜ = 0 := by
    rw [Set.compl_iInter]
    exact measure_iUnion_null hcompl
  exact (prob_compl_eq_zero_iff (MeasurableSet.iInter hmeas)).1 hnull



theorem exists_measurable_full_forall {ι : Type*} [Countable ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ι → Ω → Prop}
    (h : ∀ i, ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧ ∀ ω ∈ E, p i ω) :
    ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧ ∀ ω ∈ E, ∀ i, p i ω := by
  choose E hmeas hfull hp using h
  refine ⟨⋂ i, E i, MeasurableSet.iInter hmeas,
    measure_iInter_eq_one μ hmeas hfull, ?_⟩
  intro ω hω i
  exact hp i ω (Set.mem_iInter.1 hω i)

/-- The same conclusion when the events are already given as one family. -/
theorem exists_measurable_full_subset {ι : Type*} [Countable ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {E : ι → Set Ω}
    (hmeas : ∀ i, MeasurableSet (E i)) (hfull : ∀ i, μ (E i) = 1) :
    ∃ F : Set Ω, MeasurableSet F ∧ μ F = 1 ∧ ∀ i, F ⊆ E i :=
  ⟨⋂ i, E i, MeasurableSet.iInter hmeas,
    measure_iInter_eq_one μ hmeas hfull,
    fun i ↦ Set.iInter_subset _ i⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
