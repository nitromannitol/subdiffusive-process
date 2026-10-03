module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeChronologicalGeometry
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

noncomputable section
attribute [local instance] Classical.propDecidable



theorem card_le_card_mul_of_covered_by_bounded_fibers {α : Type*}
    (candidates selected : Finset α) (Blocks : α → α → Prop) (D : ℕ)
    (hcover : ∀ x ∈ candidates, ∃ y ∈ selected, Blocks y x)
    (hbounded : ∀ y ∈ selected, (candidates.filter (Blocks y)).card ≤ D) :
    candidates.card ≤ selected.card * D := by
  have hsubset : candidates ⊆ selected.biUnion fun y ↦ candidates.filter (Blocks y) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_filter.mpr ⟨hx, hyx⟩⟩
  exact (Finset.card_le_card hsubset).trans
    (Finset.card_biUnion_le_card_mul selected
      (fun y ↦ candidates.filter (Blocks y)) D hbounded)



theorem count_le_card_mul_of_covered_by_bounded_fibers {α : Type*}
    (candidates selected : Finset α) (Blocks : α → α → Prop) (D N : ℕ)
    (hN : N ≤ candidates.card)
    (hcover : ∀ x ∈ candidates, ∃ y ∈ selected, Blocks y x)
    (hbounded : ∀ y ∈ selected, (candidates.filter (Blocks y)).card ≤ D) :
    N ≤ selected.card * D :=
  hN.trans <| card_le_card_mul_of_covered_by_bounded_fibers
    candidates selected Blocks D hcover hbounded

/-! ## Existence of a maximal separated subfamily -/



theorem exists_pairwise_not_blocks_and_covered {α : Type*} [DecidableEq α]
    (candidates : Finset α) (Blocks : α → α → Prop)
    (hrefl : Reflexive Blocks) (hsymm : Symmetric Blocks) :
    ∃ selected : Finset α,
      selected ⊆ candidates ∧
      Set.Pairwise (selected : Set α) (fun x y ↦ ¬ Blocks x y) ∧
      ∀ x ∈ candidates, ∃ y ∈ selected, Blocks y x := by
  classical
  induction candidates using Finset.induction_on with
  | empty =>
      refine ⟨∅, Finset.Subset.rfl, ?_, ?_⟩
      · simpa only [Finset.coe_empty] using
          (Set.pairwise_empty (r := fun x y : α ↦ ¬ Blocks x y))
      intro x hx
      exact (Finset.notMem_empty x hx).elim
  | @insert a candidates ha ih =>
      obtain ⟨selected, hsubset, hpairwise, hcover⟩ := ih
      by_cases hblocked : ∃ y ∈ selected, Blocks y a
      · refine ⟨selected, hsubset.trans (Finset.subset_insert a candidates),
          hpairwise, ?_⟩
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact hblocked
        · exact hcover x hx
      · have haSelected : a ∉ selected := by
          intro haMem
          exact ha (hsubset haMem)
        refine ⟨insert a selected, ?_, ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_insert] at hx ⊢
          exact hx.imp_right fun h ↦ hsubset h
        · rw [Finset.coe_insert]
          apply hpairwise.insert_of_notMem haSelected
          intro y hy
          constructor
          · intro hay
            exact hblocked ⟨y, hy, hsymm hay⟩
          · intro hya
            exact hblocked ⟨y, hy, hya⟩
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact ⟨x, Finset.mem_insert_self x selected, hrefl x⟩
          · obtain ⟨y, hy, hyx⟩ := hcover x hx
            exact ⟨y, Finset.mem_insert_of_mem hy, hyx⟩



theorem exists_pairwise_not_blocks_with_card_bound {α : Type*} [DecidableEq α]
    (candidates : Finset α) (Blocks : α → α → Prop) (D : ℕ)
    (hrefl : Reflexive Blocks) (hsymm : Symmetric Blocks)
    (hbounded : ∀ y ∈ candidates, (candidates.filter (Blocks y)).card ≤ D) :
    ∃ selected : Finset α,
      selected ⊆ candidates ∧
      Set.Pairwise (selected : Set α) (fun x y ↦ ¬ Blocks x y) ∧
      candidates.card ≤ selected.card * D := by
  obtain ⟨selected, hsubset, hpairwise, hcover⟩ :=
    exists_pairwise_not_blocks_and_covered candidates Blocks hrefl hsymm
  refine ⟨selected, hsubset, hpairwise, ?_⟩
  exact card_le_card_mul_of_covered_by_bounded_fibers candidates selected Blocks D
    hcover fun y hy ↦ hbounded y (hsubset hy)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
