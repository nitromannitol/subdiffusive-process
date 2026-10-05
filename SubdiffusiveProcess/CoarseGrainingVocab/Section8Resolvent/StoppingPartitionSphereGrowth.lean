module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionConsumer
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

@[expose] public section

/-!
# Sphere growth for a locally finite stopping graph

The exterior-row consumer asks for a geometric upper bound on the number of
cells at each graph level.  This file derives that bound from the two natural
properties of a stopping graph: finite level sets and a uniform degree bound.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section

variable {Cell : Type*}

/-- A cell at positive source distance has a graph neighbour exactly one
level closer to the source. -/
theorem exists_adj_stoppingGraphDistance_eq_pred
    (G : SimpleGraph Cell) (hconnected : G.Connected)
    {source : Finset Cell} (hsource : source.Nonempty)
    {q : Cell} {j : ℕ}
    (hq : stoppingGraphDistance G source hsource q = j + 1) :
    ∃ p, G.Adj q p ∧ stoppingGraphDistance G source hsource p = j := by
  classical
  obtain ⟨s, hs, hqs⟩ :=
    exists_source_dist_eq_stoppingGraphDistance G hsource q
  obtain ⟨walk, hwalk⟩ := hconnected.exists_walk_length_eq_dist q s
  rw [hqs, hq] at hwalk
  have hnotnil : ¬walk.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hwalk]
    omega
  have htail : walk.tail.length = j := by
    have := walk.length_tail_add_one hnotnil
    omega
  refine ⟨walk.snd, walk.adj_snd hnotnil, le_antisymm ?_ ?_⟩
  · refine (Finset.inf'_le (fun z ↦ G.dist walk.snd z) hs).trans ?_
    exact (G.dist_le walk.tail).trans_eq htail
  · have hstep := stoppingGraphDistance_le_succ_of_adj G hconnected
      hsource (walk.adj_snd hnotnil)
    rw [hq] at hstep
    omega

/-- If finite sets enumerate the exact distance spheres, the next sphere is
contained in the union of the neighbours of the current sphere. -/
theorem stoppingLevelCells_succ_subset_biUnion_neighborFinset
    (G : SimpleGraph Cell) [DecidableEq Cell] [G.LocallyFinite]
    (hconnected : G.Connected) {source : Finset Cell}
    (hsource : source.Nonempty) (levelCells : ℕ → Finset Cell)
    (hlevel : ∀ j q, q ∈ levelCells j ↔
      stoppingGraphDistance G source hsource q = j) (j : ℕ) :
    levelCells (j + 1) ⊆
      (levelCells j).biUnion fun q ↦ G.neighborFinset q := by
  intro q hq
  obtain ⟨p, hqp, hpdist⟩ :=
    exists_adj_stoppingGraphDistance_eq_pred G hconnected hsource
      ((hlevel (j + 1) q).mp hq)
  exact Finset.mem_biUnion.mpr
    ⟨p, (hlevel j p).mpr hpdist, G.mem_neighborFinset p q |>.mpr hqp.symm⟩

/-- A recurrence in which each level is covered by at most `D` successors of
each cell gives the exponential sphere bound used by the exterior row. -/
theorem card_stoppingLevelCells_le_mul_pow [DecidableEq Cell]
    (levelCells : ℕ → Finset Cell) (next : Cell → Finset Cell)
    {N D : ℕ} (hzero : (levelCells 0).card ≤ N)
    (hnext : ∀ j, levelCells (j + 1) ⊆
      (levelCells j).biUnion next)
    (hdegree : ∀ q, (next q).card ≤ D) :
    ∀ j, (levelCells j).card ≤ N * D ^ j := by
  intro j
  induction j with
  | zero => simpa using hzero
  | succ j ih =>
      calc
        (levelCells (j + 1)).card ≤
            ((levelCells j).biUnion next).card :=
          Finset.card_le_card (hnext j)
        _ ≤ ∑ q ∈ levelCells j, (next q).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ levelCells j, D :=
          Finset.sum_le_sum fun q _ ↦ hdegree q
        _ = (levelCells j).card * D := by simp
        _ ≤ (N * D ^ j) * D := Nat.mul_le_mul_right D ih
        _ = N * D ^ (j + 1) := by simp only [pow_succ, Nat.mul_assoc]

/-- Uniformly bounded degree implies the exact sphere-growth hypothesis of
the exterior row. -/
theorem card_stoppingLevelCells_le_degree_pow
    (G : SimpleGraph Cell) [DecidableEq Cell] [G.LocallyFinite]
    (hconnected : G.Connected) {source : Finset Cell}
    (hsource : source.Nonempty) (levelCells : ℕ → Finset Cell)
    (hlevel : ∀ j q, q ∈ levelCells j ↔
      stoppingGraphDistance G source hsource q = j)
    {N D : ℕ} (hsourceCard : (levelCells 0).card ≤ N)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D) :
    ∀ j, (levelCells j).card ≤ N * D ^ j :=
  card_stoppingLevelCells_le_mul_pow levelCells (fun q ↦ G.neighborFinset q) hsourceCard
    (stoppingLevelCells_succ_subset_biUnion_neighborFinset
      G hconnected hsource levelCells hlevel) hdegree

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
