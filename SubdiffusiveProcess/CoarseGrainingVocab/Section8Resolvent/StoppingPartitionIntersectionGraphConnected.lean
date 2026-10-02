import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedProducer
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectivity of an intersection-supergraph

An open cover of a connected space has connected intersection graph whenever
every actual intersection is an edge.  This supplies the connectivity input
used by graph-distance and exterior-row arguments for the repaired cells.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

/-- A graph containing every intersection edge of a nonempty open cover of a
preconnected space is connected. -/
theorem simpleGraph_connected_of_open_cover_of_intersection_edge
    [Nonempty I] (cell : I → Set X) (hopen : ∀ q, IsOpen (cell q))
    (hnonempty : ∀ q, (cell q).Nonempty)
    (hcover : (⋃ q, cell q) = Set.univ) (G : SimpleGraph I)
    (hintersection : ∀ {q p}, q ≠ p → (cell q ∩ cell p).Nonempty →
      G.Adj q p) :
    G.Connected := by
  refine ⟨?_⟩
  intro u v
  by_contra huvReachable
  let reachable : Set I := {q | G.Reachable u q}
  let unreachable : Set I := {q | ¬ G.Reachable u q}
  let U : Set X := ⋃ q : reachable, cell q.1
  let V : Set X := ⋃ q : unreachable, cell q.1
  have hUOpen : IsOpen U := isOpen_iUnion fun q ↦ hopen q.1
  have hVOpen : IsOpen V := isOpen_iUnion fun q ↦ hopen q.1
  have hUV : Set.univ ⊆ U ∪ V := by
    intro x _
    have hx : x ∈ ⋃ q, cell q := by rw [hcover]; trivial
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    by_cases hq : G.Reachable u q
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩)
  have hdisjoint : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxV
    have hqp : q.1 ≠ p.1 := by
      intro heq
      exact p.2 (heq ▸ q.2)
    have hadj : G.Adj q.1 p.1 :=
      hintersection hqp ⟨x, hxq, hxp⟩
    exact p.2 (q.2.trans hadj.reachable)
  have hU : U.Nonempty := by
    obtain ⟨x, hxu⟩ := hnonempty u
    exact ⟨x, Set.mem_iUnion.mpr ⟨⟨u, SimpleGraph.Reachable.refl u⟩, hxu⟩⟩
  have hV : V.Nonempty := by
    obtain ⟨x, hxv⟩ := hnonempty v
    exact ⟨x, Set.mem_iUnion.mpr ⟨⟨v, huvReachable⟩, hxv⟩⟩
  rcases isPreconnected_univ.subset_or_subset hUOpen hVOpen hdisjoint hUV with
    hunivU | hunivV
  · obtain ⟨x, hxV⟩ := hV
    exact Set.disjoint_left.mp hdisjoint (hunivU trivial) hxV
  · obtain ⟨x, hxU⟩ := hU
    exact Set.disjoint_left.mp hdisjoint hxU (hunivV trivial)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
