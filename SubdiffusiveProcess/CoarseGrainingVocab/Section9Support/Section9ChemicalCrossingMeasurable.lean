module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalGoodSiteDecoupling

@[expose] public section

/-!
# Measurability of the crossing-density failure event

`CrossingGoodCount` quantifies over `J`-step paths (a countable type of lists),
over finite sets of vertices (countable), and, inside `AnnulusGoodSite`, over
scales and influence-box centres (countable).  Every quantifier is therefore
countable and the event is measurable as soon as the field's events are.  This is
what the minimal-scale construction of the crossing clause needs.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*}

theorem measurableSet_annulusGoodSite [MeasurableSpace Ω]
    {E : ℕ → Lattice d → Set Ω} (hE : ∀ j z, MeasurableSet (E j z))
    (Cbox : ℕ) (z : Lattice d) (l : ℕ) (v : Lattice d) :
    MeasurableSet {ω | AnnulusGoodSite E Cbox ω z l v} := by
  by_cases hbox : latticeBallSet v Cbox ⊆
      latticeBallSet z (3 * l / 4 : ℝ) \ latticeBallSet z (l / 4 : ℝ)
  · have hset : {ω | AnnulusGoodSite E Cbox ω z l v} =
        (percolationBadSite E Cbox v)ᶜ := by
      ext ω
      simp only [AnnulusGoodSite, Set.mem_ofPred_eq, Set.mem_compl_iff,
        percolationBadSite, not_not]
      exact ⟨fun h => h.1, fun h => ⟨h, hbox⟩⟩
    rw [hset]
    exact (measurableSet_percolationBadSite E hE v).compl
  · have hset : {ω | AnnulusGoodSite E Cbox ω z l v} = ∅ := by
      ext ω
      simp only [AnnulusGoodSite, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      exact fun _ => hbox
    rw [hset]
    exact MeasurableSet.empty

/-- The crossing-density failure event is measurable. -/
theorem measurableSet_crossFailEvent [MeasurableSpace Ω]
    {E : ℕ → Lattice d → Set Ω} (hE : ∀ j z, MeasurableSet (E j z))
    (Cbox J : ℕ) (z : Lattice d) (l N : ℕ) :
    MeasurableSet (crossFailEvent E Cbox J z l N) := by
  classical
  set F : List (Lattice d) → Set Ω := fun path =>
    if IsJStepListPath J path ∧
        (∃ v ∈ path, InLatticeBallReal z v ((l : ℝ) / 3)) ∧
        (∃ v ∈ path, ¬ InLatticeBallReal z v (2 * (l : ℝ) / 3)) then
      ⋃ S : Finset (Lattice d), ⋃ _ : (∀ v ∈ S, v ∈ path) ∧ N ≤ S.card,
        ⋂ v ∈ S, {ω | AnnulusGoodSite E Cbox ω z l v}
    else Set.univ with hF
  have hFmeas : ∀ path, MeasurableSet (F path) := by
    intro path
    simp only [hF]
    by_cases hval : IsJStepListPath J path ∧
        (∃ v ∈ path, InLatticeBallReal z v ((l : ℝ) / 3)) ∧
        (∃ v ∈ path, ¬ InLatticeBallReal z v (2 * (l : ℝ) / 3))
    · rw [ite_eq_left hval]
      refine MeasurableSet.iUnion fun S => MeasurableSet.iUnion fun _ => ?_
      exact Finset.measurableSet_biInter S fun v _ =>
        measurableSet_annulusGoodSite hE Cbox z l v
    · rw [ite_eq_right hval]
      exact MeasurableSet.univ
  have hset : (crossFailEvent E Cbox J z l N)ᶜ = ⋂ path : List (Lattice d), F path := by
    ext ω
    simp only [crossFailEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not,
      Set.mem_iInter]
    constructor
    · intro hgc path
      simp only [hF]
      by_cases hval : IsJStepListPath J path ∧
          (∃ v ∈ path, InLatticeBallReal z v ((l : ℝ) / 3)) ∧
          (∃ v ∈ path, ¬ InLatticeBallReal z v (2 * (l : ℝ) / 3))
      · rw [ite_eq_left hval]
        obtain ⟨S, hS1, hS2, hS3⟩ := hgc path hval.1 hval.2.1 hval.2.2
        refine Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨⟨hS1, hS3⟩, ?_⟩⟩
        exact Set.mem_iInter₂.mpr fun v hv => hS2 v hv
      · rw [ite_eq_right hval]
        exact Set.mem_univ _
    · intro hall path hpath hstart hexit
      have h := hall path
      simp only [hF] at h
      rw [ite_eq_left ⟨hpath, hstart, hexit⟩] at h
      obtain ⟨S, hS⟩ := Set.mem_iUnion.mp h
      obtain ⟨hcond, hmem⟩ := Set.mem_iUnion.mp hS
      exact ⟨S, hcond.1, fun v hv => Set.mem_iInter₂.mp hmem v hv, hcond.2⟩
  have hcompl : MeasurableSet (crossFailEvent E Cbox J z l N)ᶜ := by
    rw [hset]
    exact MeasurableSet.iInter hFmeas
  exact hcompl.of_compl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
