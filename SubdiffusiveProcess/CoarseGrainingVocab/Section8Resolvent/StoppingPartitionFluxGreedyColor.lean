module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFluxColoring

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Cell : Type*} [Encodable Cell] [DecidableEq Cell]

/-- Choose a color outside a finite used set when one exists. -/
def stoppingFirstFreeColor (D : ℕ) (used : Finset (Fin (D + 1))) :
    Fin (D + 1) :=
  if h : ∃ c, c ∉ used then Classical.choose h else 0

theorem stoppingFirstFreeColor_not_mem {D : ℕ}
    {used : Finset (Fin (D + 1))} (hcard : used.card ≤ D) :
    stoppingFirstFreeColor D used ∉ used := by
  have havailable : ∃ c, c ∉ used := by
    by_contra hall
    push_neg at hall
    have huniv : Finset.univ ⊆ used := fun c _ ↦ hall c
    have := Finset.card_le_card huniv
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [stoppingFirstFreeColor, dif_pos havailable]
  exact Classical.choose_spec havailable

/-- Colors used by earlier adjacent vertices in the canonical encoding
order. -/
def stoppingEarlierNeighborColors (G : SimpleGraph Cell) (D : ℕ) (q : Cell)
    (previousColor : ∀ p : Cell, Encodable.encode p < Encodable.encode q →
      Fin (D + 1)) : Finset (Fin (D + 1)) :=
  ((stoppingCellExhaustion (Encodable.encode q)).filter (G.Adj q)).image
    fun p ↦ if hp : Encodable.encode p < Encodable.encode q then
      previousColor p hp else 0

set_option linter.unusedSectionVars false in
theorem card_stoppingEarlierNeighborColors_le
    (G : SimpleGraph Cell) [G.LocallyFinite] {D : ℕ}
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D)
    (q : Cell)
    (previousColor : ∀ p : Cell, Encodable.encode p < Encodable.encode q →
      Fin (D + 1)) :
    (stoppingEarlierNeighborColors G D q previousColor).card ≤ D := by
  calc
    (stoppingEarlierNeighborColors G D q previousColor).card ≤
        ((stoppingCellExhaustion (Encodable.encode q)).filter
          (G.Adj q)).card := Finset.card_image_le
    _ ≤ (G.neighborFinset q).card := by
      apply Finset.card_le_card
      intro p hp
      rw [G.mem_neighborFinset]
      exact (Finset.mem_filter.mp hp).2
    _ ≤ D := hdegree q

/-- One recursive greedy-coloring step. -/
def stoppingGreedyColorStep (G : SimpleGraph Cell) (D : ℕ) (q : Cell)
    (previousColor : ∀ p : Cell, Encodable.encode p < Encodable.encode q →
      Fin (D + 1)) : Fin (D + 1) :=
  stoppingFirstFreeColor D
    (stoppingEarlierNeighborColors G D q previousColor)

/-- Greedy coloring in canonical encoding order. -/
def stoppingGreedyColor (G : SimpleGraph Cell) (D : ℕ) :
    Cell → Fin (D + 1) :=
  (measure (fun q : Cell ↦ Encodable.encode q)).wf.fix
    (stoppingGreedyColorStep G D)

theorem stoppingGreedyColor_not_mem_earlier
    (G : SimpleGraph Cell) [G.LocallyFinite] {D : ℕ}
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D) (q : Cell) :
    stoppingGreedyColor G D q ∉
      ((stoppingCellExhaustion (Encodable.encode q)).filter (G.Adj q)).image
        (stoppingGreedyColor G D) := by
  have hfix : stoppingGreedyColor G D q =
      stoppingGreedyColorStep G D q
        (fun p _ ↦ stoppingGreedyColor G D p) := by
    rw [stoppingGreedyColor, WellFounded.fix_eq]
    congr 1
  rw [hfix]
  unfold stoppingGreedyColorStep
  intro hused
  apply stoppingFirstFreeColor_not_mem
    (card_stoppingEarlierNeighborColors_le G hdegree q
      (fun p _ ↦ stoppingGreedyColor G D p))
  obtain ⟨p, hp, hpcolor⟩ := Finset.mem_image.mp hused
  apply Finset.mem_image.mpr
  refine ⟨p, hp, ?_⟩
  rw [dif_pos (mem_stoppingCellExhaustion_iff.mp
    (Finset.mem_filter.mp hp).1)]
  exact hpcolor

/-- A countable graph of degree at most `D` has a canonical proper coloring
with `D + 1` colors. -/
def stoppingBoundedDegreeColoring
    (G : SimpleGraph Cell) [G.LocallyFinite] (D : ℕ)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D) :
    G.Coloring (Fin (D + 1)) :=
  SimpleGraph.Coloring.mk (stoppingGreedyColor G D) fun {q p} hadj ↦ by
    have hqp : q ≠ p := G.ne_of_adj hadj
    rcases lt_or_gt_of_ne (Encodable.encode_injective.ne hqp) with hpq | hqp'
    · intro heq
      apply stoppingGreedyColor_not_mem_earlier G hdegree p
      apply Finset.mem_image.mpr
      refine ⟨q, Finset.mem_filter.mpr
        ⟨mem_stoppingCellExhaustion_iff.mpr hpq, hadj.symm⟩, heq⟩
    · intro heq
      apply stoppingGreedyColor_not_mem_earlier G hdegree q
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_filter.mpr
        ⟨mem_stoppingCellExhaustion_iff.mpr hqp', hadj⟩, heq.symm⟩

/-- Bounded degree plus containment of the cell-intersection graph gives the
finite disjoint-color decomposition consumed by `FluxRowRieszPartition`. -/
theorem pairwiseDisjoint_filtered_cells_of_boundedDegree
    {X : Type*} (cells : Finset Cell) (cell : Cell → Set X)
    (G : SimpleGraph Cell) [G.LocallyFinite] (D : ℕ)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D)
    (hintersection : ∀ {q p}, q ≠ p →
      (cell q ∩ cell p).Nonempty → G.Adj q p)
    (k : Fin (D + 1)) :
    ((cells.filter fun q ↦ stoppingBoundedDegreeColoring G D hdegree q = k :
      Finset Cell) : Set Cell).PairwiseDisjoint cell :=
  pairwiseDisjoint_filtered_cells_of_intersectionGraphColoring cells cell G
    (stoppingBoundedDegreeColoring G D hdegree) hintersection k

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
