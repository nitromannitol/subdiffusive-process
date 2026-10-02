import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CountableFullEvents
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.FiniteCutoffConclusion

/-!
# The outer structure of the `C^{0,γ}` clause (B5)

Theorem C's `C^{0,γ}` clause has a specific binder order
(`SubdiffusiveProcess/Frozen/Section6/LargeScaleHolderMultifractal.lean`):

```lean
∀ gamma ∈ Set.Icc (1/2) (gammaReg C0 M.delta),
  ∃ full : Set (AnchoredC11Sample d),
    MeasurableSet full ∧ (…).toMeasure full = 1 ∧
    ∀ L : WithTop ℕ, ∀ m : ℕ, 0 < m →
      ∃ X : AnchoredC11Sample d → ℕ, … ∧ ∀ ω ∈ full, …
```

The probability-one event `full` is introduced **before** `∀ L` and `∀ m`, so a
single event must serve every cutoff and every scale simultaneously, while the
minimal-scale witness `X` may depend on both.  This is the D-011/R27 reading.

Producing that shape from per-`(L,m)` data is the content of this file: the
event has to be *hoisted out* of the index quantifier, which is legitimate
because the index type `WithTop ℕ × ℕ` is countable, so the intersection of the
per-index events is still probability one (`CountableFullEvents`).

`exists_full_forall_index` is the generic hoist; `exists_full_forall_cutoff_scale`
is it at Theorem C's index type.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **B5, the hoist.**  If for every index there is a probability-one event
carrying a witness, then a *single* probability-one event carries a witness for
every index at once. -/
theorem exists_full_forall_index {ι A : Type*} [Countable ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : ι → A → Prop} {R : ι → A → Ω → Prop}
    (h : ∀ i, ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
      ∃ a : A, S i a ∧ ∀ ω ∈ E, R i a ω) :
    ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
      ∀ i, ∃ a : A, S i a ∧ ∀ ω ∈ E, R i a ω := by
  choose E hmeas hfull a hS hR using h
  refine ⟨⋂ i, E i, MeasurableSet.iInter hmeas,
    measure_iInter_eq_one μ hmeas hfull, ?_⟩
  intro i
  exact ⟨a i, hS i, fun ω hω ↦ hR i ω (Set.mem_iInter.1 hω i)⟩

/-- Theorem C's index type is countable, so the hoist applies. -/
example : Countable (WithTop ℕ × ℕ) := inferInstance

/-- **B5 at Theorem C's index type.**  A single probability-one event serving
every cutoff `L : WithTop ℕ` and every scale `m : ℕ`, with the minimal-scale
witness depending on both. -/
theorem exists_full_forall_cutoff_scale {A : Type*}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : WithTop ℕ → ℕ → A → Prop} {R : WithTop ℕ → ℕ → A → Ω → Prop}
    (h : ∀ (L : WithTop ℕ) (m : ℕ), ∃ E : Set Ω,
      MeasurableSet E ∧ μ E = 1 ∧
        ∃ a : A, S L m a ∧ ∀ ω ∈ E, R L m a ω) :
    ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
      ∀ (L : WithTop ℕ) (m : ℕ), ∃ a : A, S L m a ∧ ∀ ω ∈ E, R L m a ω := by
  obtain ⟨E, hmeas, hfull, hall⟩ :=
    exists_full_forall_index (ι := WithTop ℕ × ℕ) (A := A) μ
      (S := fun p a ↦ S p.1 p.2 a) (R := fun p a ↦ R p.1 p.2 a)
      (fun p ↦ h p.1 p.2)
  exact ⟨E, hmeas, hfull, fun L m ↦ hall (L, m)⟩

/-- The same hoist when the per-index statement additionally carries a
positivity side condition on the scale, as Theorem C's `0 < m` does. -/
theorem exists_full_forall_cutoff_scale_pos {A : Type*}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : WithTop ℕ → ℕ → A → Prop} {R : WithTop ℕ → ℕ → A → Ω → Prop}
    (h : ∀ (L : WithTop ℕ) (m : ℕ), 0 < m → ∃ E : Set Ω,
      MeasurableSet E ∧ μ E = 1 ∧
        ∃ a : A, S L m a ∧ ∀ ω ∈ E, R L m a ω)
    (a0 : A) :
    ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
      ∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
        ∃ a : A, S L m a ∧ ∀ ω ∈ E, R L m a ω := by
  classical
  obtain ⟨E, hmeas, hfull, hall⟩ :=
    exists_full_forall_cutoff_scale (A := A) μ
      (S := fun L m a ↦ 0 < m → S L m a)
      (R := fun L m a ω ↦ 0 < m → R L m a ω)
      (fun L m ↦ by
        by_cases hm : 0 < m
        · obtain ⟨E, hE1, hE2, a, hS, hR⟩ := h L m hm
          exact ⟨E, hE1, hE2, a, fun _ ↦ hS, fun ω hω _ ↦ hR ω hω⟩
        · exact ⟨Set.univ, MeasurableSet.univ, measure_univ, a0,
            fun hc ↦ absurd hc hm, fun _ _ hc ↦ absurd hc hm⟩)
  refine ⟨E, hmeas, hfull, fun L m hm ↦ ?_⟩
  obtain ⟨a, hS, hR⟩ := hall L m
  exact ⟨a, hS hm, fun ω hω ↦ hR ω hω hm⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
