import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFluxOwnership
import Mathlib.Combinatorics.SimpleGraph.Coloring




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set

noncomputable section
attribute [local instance] Classical.propDecidable

variable {X Cell Color : Type*}

/-- A proper graph coloring separates every pair of intersecting cells when
the graph contains the intersection graph. -/
theorem pairwiseDisjoint_cells_of_intersectionGraphColoring
    (cell : Cell → Set X) (G : SimpleGraph Cell) (C : G.Coloring Color)
    (hintersection : ∀ {q p}, q ≠ p → (cell q ∩ cell p).Nonempty → G.Adj q p)
    (k : Color) :
    (C.colorClass k).PairwiseDisjoint cell := by
  rw [Set.pairwiseDisjoint_iff]
  intro q hq p hp hnonempty
  by_contra hqp
  exact C.valid (hintersection hqp hnonempty) (hq.trans hp.symm)

/-- Restricting a disjoint color class to a finite exhaustion preserves
pairwise disjointness. -/
theorem pairwiseDisjoint_filtered_cells_of_intersectionGraphColoring
    [DecidableEq Cell] [DecidableEq Color]
    (cells : Finset Cell) (cell : Cell → Set X)
    (G : SimpleGraph Cell) (C : G.Coloring Color)
    (hintersection : ∀ {q p}, q ≠ p → (cell q ∩ cell p).Nonempty → G.Adj q p)
    (k : Color) :
    ((cells.filter fun q ↦ C q = k : Finset Cell) : Set Cell).PairwiseDisjoint
      cell := by
  rw [Set.pairwiseDisjoint_iff]
  intro q hq p hp hnonempty
  apply Set.pairwiseDisjoint_iff.mp
    (pairwiseDisjoint_cells_of_intersectionGraphColoring cell G C
      hintersection k)
  · exact (Finset.mem_filter.mp hq).2
  · exact (Finset.mem_filter.mp hp).2
  · exact hnonempty

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
