module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeGreedySelection
public import Mathlib.Data.Finset.Pairwise

@[expose] public section

/-!
# Chronological separated selection from a finite path

After chronological loop erasure, the path  has distinct
vertices. A maximal independent set of its good vertices gives the required separated cubes;
filtering the original list by that set preserves chronological order. This file formalizes
that exact finite combinatorial step.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A loop-free chronological list has a chronological pairwise nonblocking sublist containing
at least a `1 / D` fraction of its good vertices, in integral form.

`Blocks x y` represents intersection of the fixed dilates of the two cubes. The fiber bound is
the finite-degree input of the periodic graph.

-/
theorem exists_chronological_pairwise_not_blocks {α : Type*} [DecidableEq α]
    (q : List α) (hq : q.Nodup) (good : Set α) (Blocks : α → α → Prop) (D : ℕ)
    (hrefl : ∀ x : α, Blocks x x)
    (hsymm : ∀ ⦃x y : α⦄, Blocks x y → Blocks y x)
    (hbounded : ∀ y ∈ q.toFinset.filter (· ∈ good),
      ((q.toFinset.filter (· ∈ good)).filter (Blocks y)).card ≤ D) :
    ∃ selected : List α,
      selected.Sublist q ∧
      selected.Pairwise (fun x y ↦ ¬ Blocks x y) ∧
      (q.toFinset.filter (· ∈ good)).card ≤ selected.length * D ∧
      ∀ x ∈ selected, x ∈ good := by
  classical
  let candidates := q.toFinset.filter (· ∈ good)
  obtain ⟨chosen, hchosen, hpairwise, hcard⟩ :=
    exists_pairwise_not_blocks_with_card_bound candidates Blocks D hrefl hsymm
      (by simpa only [candidates] using hbounded)
  let selected := q.filter fun x ↦ decide (x ∈ chosen)
  have hchosenQ : chosen ⊆ q.toFinset :=
    hchosen.trans (Finset.filter_subset _ _)
  have hselectedFinset : selected.toFinset = chosen := by
    ext x
    rw [List.mem_toFinset]
    constructor
    · intro hx
      have hxChosen : decide (x ∈ chosen) := (List.mem_filter.mp hx).2
      simpa only [decide_eq_true_eq] using hxChosen
    · intro hxChosen
      apply List.mem_filter.mpr
      refine ⟨List.mem_toFinset.mp (hchosenQ hxChosen), ?_⟩
      simpa only [decide_eq_true_eq]
  have hselectedNodup : selected.Nodup := hq.filter _
  have hselectedPairwise : selected.Pairwise (fun x y ↦ ¬ Blocks x y) := by
    apply List.pairwise_of_coe_toFinset_pairwise _ hselectedNodup
    rw [hselectedFinset]
    exact hpairwise
  have hselectedCard : chosen.card = selected.length := by
    rw [← hselectedFinset]
    exact List.toFinset_card_of_nodup hselectedNodup
  refine ⟨selected, List.filter_sublist, hselectedPairwise, ?_, ?_⟩
  · simpa only [candidates, hselectedCard] using hcard
  · intro x hx
    have hxChosen : x ∈ chosen := by
      have hxDecide : decide (x ∈ chosen) := (List.mem_filter.mp hx).2
      simpa only [decide_eq_true_eq] using hxDecide
    have hxCandidate : x ∈ candidates := hchosen hxChosen
    exact (Finset.mem_filter.mp hxCandidate).2

/-- If at least `N` distinct vertices of the loop-erased path are good, the selected
chronological sublist satisfies `N ≤ selected.length * D`.

Source: the `cN` conclusion, proved by the bounded-degree
argument at `13290-13298`.
-/
theorem exists_chronological_pairwise_not_blocks_of_count {α : Type*} [DecidableEq α]
    (q : List α) (hq : q.Nodup) (good : Set α) (Blocks : α → α → Prop) (D N : ℕ)
    (hrefl : ∀ x : α, Blocks x x)
    (hsymm : ∀ ⦃x y : α⦄, Blocks x y → Blocks y x)
    (hN : N ≤ (q.filter fun x ↦ decide (x ∈ good)).length)
    (hbounded : ∀ y ∈ q.toFinset.filter (· ∈ good),
      ((q.toFinset.filter (· ∈ good)).filter (Blocks y)).card ≤ D) :
    ∃ selected : List α,
      selected.Sublist q ∧
      selected.Pairwise (fun x y ↦ ¬ Blocks x y) ∧
      N ≤ selected.length * D ∧
      ∀ x ∈ selected, x ∈ good := by
  obtain ⟨selected, hsublist, hpairwise, hcard, hgood⟩ :=
    exists_chronological_pairwise_not_blocks q hq good Blocks D hrefl hsymm hbounded
  refine ⟨selected, hsublist, hpairwise, ?_, hgood⟩
  apply hN.trans
  have hfilterNodup : (q.filter fun x ↦ decide (x ∈ good)).Nodup := hq.filter _
  rw [← List.toFinset_card_of_nodup hfilterNodup]
  simpa only [List.toFinset_filter, decide_eq_true_eq] using hcard

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
