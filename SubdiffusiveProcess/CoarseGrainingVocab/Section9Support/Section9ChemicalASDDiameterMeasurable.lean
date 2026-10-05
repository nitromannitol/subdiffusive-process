module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDDiameterGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalGoodSiteDecoupling

@[expose] public section

/-!
# Measurability of the `[ASD]` bad-component failure events

`badComponentFailureEvent` quantifies over lattice sites, over the finite `1`-step
paths realising a bad component, and over pairs of component sites — all of them
**countable** families, because `Lattice d = Fin d → ℤ` is countable and so is
`List (Lattice d)`.  This file writes each of those quantifiers as a countable
union or intersection of events of the field, and concludes that
`badComponentFailureEvent` is measurable whenever every `E j z` is.

Measurability is what the `O_{Γ₁}` convention of `SubdiffusiveProcess.OGammaLE` needs: the
minimal scale built from these events in
`Section9ChemicalASDDiameterTail` has to be a genuine random variable.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The reachability event inside the bad set is a countable union over the
`1`-step paths of finite intersections of bad-site events. -/
theorem jStepReachable_eq_iUnion (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ)
    (v a : Lattice d) :
    {ω : Ω | JStepReachableIn J {u | ¬ IsPercolationGoodSite E Cbox ω u} v a} =
      ⋃ path ∈ {p : List (Lattice d) |
          p.head? = some v ∧ p.getLast? = some a ∧ IsJStepListPath J p},
        ⋂ u ∈ path, percolationBadSite E Cbox u := by
  ext ω
  constructor
  · rintro ⟨path, h1, h2, h3, h4⟩
    exact Set.mem_iUnion₂.mpr ⟨path, ⟨h1, h2, h3⟩,
      Set.mem_iInter₂.mpr fun u hu => h4 u hu⟩
  · intro hω
    obtain ⟨path, ⟨h1, h2, h3⟩, h4⟩ := Set.mem_iUnion₂.mp hω
    exact ⟨path, h1, h2, h3, fun u hu => Set.mem_iInter₂.mp h4 u hu⟩

theorem measurableSet_jStepReachable {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox J : ℕ) (v a : Lattice d) :
    MeasurableSet
      {ω : Ω | JStepReachableIn J {u | ¬ IsPercolationGoodSite E Cbox ω u} v a} := by
  rw [jStepReachable_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun path _ => ?_
  exact MeasurableSet.biInter (Set.to_countable _) fun u _ =>
    measurableSet_percolationBadSite (Cbox := Cbox) _ hE u

omit [MeasurableSpace Ω] in
/-- The failure of the diameter bound is a countable union over the pairs of
component sites that realise it. -/
theorem notDiameter_eq_iUnion (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ)
    (v : Lattice d) (R : ℝ) :
    {ω : Ω | ¬ HasLatticeDiameterAtMost
        (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox ω u} v) R} =
      ⋃ ab ∈ {p : Lattice d × Lattice d |
          ∃ i : Fin d, ¬ ((|p.1 i - p.2 i| : ℤ) : ℝ) ≤ R},
        ({ω : Ω | JStepReachableIn J {u | ¬ IsPercolationGoodSite E Cbox ω u} v ab.1} ∩
          {ω : Ω | JStepReachableIn J {u | ¬ IsPercolationGoodSite E Cbox ω u} v ab.2}) := by
  ext ω
  constructor
  · intro hω
    simp only [mem_ofPred_eq, HasLatticeDiameterAtMost] at hω
    push Not at hω
    obtain ⟨a, ha, b, hb, i, hab⟩ := hω
    exact Set.mem_iUnion₂.mpr ⟨(a, b), ⟨i, not_le.mpr hab⟩, ha, hb⟩
  · intro hω
    obtain ⟨ab, ⟨i, hi⟩, ha, hb⟩ := Set.mem_iUnion₂.mp hω
    intro hdiam
    exact hi (hdiam ab.1 ha ab.2 hb i)

theorem measurableSet_notDiameter {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox J : ℕ) (v : Lattice d) (R : ℝ) :
    MeasurableSet
      {ω : Ω | ¬ HasLatticeDiameterAtMost
        (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox ω u} v) R} := by
  rw [notDiameter_eq_iUnion]
  exact MeasurableSet.biUnion (Set.to_countable _) fun ab _ =>
    (measurableSet_jStepReachable hE Cbox J v ab.1).inter
      (measurableSet_jStepReachable hE Cbox J v ab.2)

/-- **The `[ASD]` failure event is measurable.** -/
theorem measurableSet_badComponentFailureEvent {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox J : ℕ) (z : Lattice d) (s R : ℝ) :
    MeasurableSet (badComponentFailureEvent E Cbox J z s R) := by
  have heq : badComponentFailureEvent E Cbox J z s R =
      ⋃ v ∈ {v : Lattice d | InLatticeBallReal z v s},
        (percolationBadSite E Cbox v ∩
          {ω : Ω | ¬ HasLatticeDiameterAtMost
            (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox ω u} v) R}) := by
    ext ω
    constructor
    · rintro ⟨v, hv, hbad, hdiam⟩
      exact Set.mem_iUnion₂.mpr ⟨v, hv, hbad, hdiam⟩
    · intro hω
      obtain ⟨v, hv, hbad, hdiam⟩ := Set.mem_iUnion₂.mp hω
      exact ⟨v, hv, hbad, hdiam⟩
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable _) fun v _ =>
    (measurableSet_percolationBadSite (Cbox := Cbox) _ hE v).inter
      (measurableSet_notDiameter hE Cbox J v R)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
