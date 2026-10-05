module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedConnected
public import Mathlib.Topology.Compactness.LocallyFinite

@[expose] public section

/-!
# Neighbor covers for repaired stopping cells

The finite half-grid refinement is a global open cover.  Any refined cell
meeting the centered enlargement of another has near selected parents and is
therefore either that cell or a graph neighbor.  Thus the closed graph
neighborhood gives the finite enlargement cover required by the exterior row.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

omit [NeZero d] in
/-- A refined cell meeting another refined cell's enlargement has near
selected parent cubes. -/
theorem stoppingCubesNear_of_refinedStoppingCell_meets_enlargement
    {q p : RefinedStoppingCell failure omega base}
    (hinter :
      (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p)
          (refinedStoppingCenter p)).Nonempty) :
    StoppingCubesNear (refinedStoppingFailureCube q)
      (refinedStoppingFailureCube p) := by
  obtain ⟨x, hxq, hxp⟩ := hinter
  let sq := cubeScaleFactor (refinedStoppingFailureCube q)
  let sp := cubeScaleFactor (refinedStoppingFailureCube p)
  have hqShift := dist_cubeCenter_refinedStoppingCenter_le q
  have hpShift := dist_cubeCenter_refinedStoppingCenter_le p
  have hqx := (dist_refinedStoppingCenter_lt_of_mem_enlargement hxq).le
  have hpx := (dist_refinedStoppingCenter_lt_of_mem hxp).le
  have hpath : dist (cubeCenter (refinedStoppingFailureCube q))
      (cubeCenter (refinedStoppingFailureCube p)) ≤
      (3 / 2 * sq + 3 / 2 * sq) + (1 / 2 * sp + 3 / 2 * sp) := by
    calc
      dist (cubeCenter (refinedStoppingFailureCube q))
          (cubeCenter (refinedStoppingFailureCube p)) ≤
          dist (cubeCenter (refinedStoppingFailureCube q))
              (refinedStoppingCenter q) +
            dist (refinedStoppingCenter q)
              (cubeCenter (refinedStoppingFailureCube p)) :=
        dist_triangle _ _ _
      _ ≤ dist (cubeCenter (refinedStoppingFailureCube q))
              (refinedStoppingCenter q) +
            (dist (refinedStoppingCenter q) x +
              dist x (cubeCenter (refinedStoppingFailureCube p))) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ dist (cubeCenter (refinedStoppingFailureCube q))
              (refinedStoppingCenter q) +
            (dist (refinedStoppingCenter q) x +
              (dist x (refinedStoppingCenter p) +
                dist (refinedStoppingCenter p)
                  (cubeCenter (refinedStoppingFailureCube p)))) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ (3 / 2 * sq + 3 / 2 * sq) +
          (1 / 2 * sp + 3 / 2 * sp) := by
        have hpx' : dist x (refinedStoppingCenter p) ≤
            1 / 2 * cubeScaleFactor (refinedStoppingFailureCube p) := by
          rwa [dist_comm]
        have hpShift' : dist (refinedStoppingCenter p)
              (cubeCenter (refinedStoppingFailureCube p)) ≤
            3 / 2 * cubeScaleFactor (refinedStoppingFailureCube p) := by
          rwa [dist_comm]
        dsimp only [sq, sp] at hqShift hpShift hqx hpx hpx' hpShift' ⊢
        linarith
  unfold StoppingCubesNear
  dsimp only [sq, sp] at hpath
  have hq := le_max_left
    (cubeScaleFactor (refinedStoppingFailureCube q))
    (cubeScaleFactor (refinedStoppingFailureCube p))
  have hp := le_max_right
    (cubeScaleFactor (refinedStoppingFailureCube q))
    (cubeScaleFactor (refinedStoppingFailureCube p))
  have hmax : 0 ≤ max (cubeScaleFactor (refinedStoppingFailureCube q))
      (cubeScaleFactor (refinedStoppingFailureCube p)) :=
    (zpow_pos (show (0 : ℝ) < 3 by norm_num) _).le.trans hq
  calc
    dist (cubeCenter (refinedStoppingFailureCube q))
        (cubeCenter (refinedStoppingFailureCube p)) ≤
        (3 / 2 * cubeScaleFactor (refinedStoppingFailureCube q) +
          3 / 2 * cubeScaleFactor (refinedStoppingFailureCube q)) +
        (1 / 2 * cubeScaleFactor (refinedStoppingFailureCube p) +
          3 / 2 * cubeScaleFactor (refinedStoppingFailureCube p)) := hpath
    _ ≤ 10 * max (cubeScaleFactor (refinedStoppingFailureCube q))
        (cubeScaleFactor (refinedStoppingFailureCube p)) := by linarith

omit [NeZero d] in
/-- A distinct refined cell meeting an enlargement is adjacent in the
repaired graph. -/
theorem repairedStoppingGraph_adj_of_meets_enlargement
    {q p : RefinedStoppingCell failure omega base} (hne : q ≠ p)
    (hinter :
      (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p)
          (refinedStoppingCenter p)).Nonempty) :
    repairedStoppingGraph.Adj q p :=
  (repairedStoppingGraph_adj_iff q p).mpr
    ⟨hne, stoppingCubesNear_of_refinedStoppingCell_meets_enlargement hinter⟩

/-- The cell together with all of its graph neighbors. -/
def repairedStoppingClosedNeighbors
    (q : RefinedStoppingCell failure omega base) :
    Finset (RefinedStoppingCell failure omega base) :=
  insert q (repairedStoppingGraph.neighborFinset q)

theorem repairedStoppingClosedNeighbors_nonempty
    (q : RefinedStoppingCell failure omega base) :
    (repairedStoppingClosedNeighbors q).Nonempty :=
  ⟨q, Finset.mem_insert_self q _⟩

/-- The closed graph neighborhood has a dimension-only cardinality bound. -/
theorem card_repairedStoppingClosedNeighbors_le
    (q : RefinedStoppingCell failure omega base) :
    (repairedStoppingClosedNeighbors q).card ≤
      repairedStoppingDegreeBound d + 1 := by
  unfold repairedStoppingClosedNeighbors
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right
      (card_repairedStoppingGraph_neighborFinset_le q) 1)

/-- Every member of the closed neighborhood is the center cell or an actual
graph neighbor. -/
theorem eq_or_adj_of_mem_repairedStoppingClosedNeighbors
    {q p : RefinedStoppingCell failure omega base}
    (hp : p ∈ repairedStoppingClosedNeighbors q) :
    p = q ∨ repairedStoppingGraph.Adj q p := by
  rw [repairedStoppingClosedNeighbors, Finset.mem_insert] at hp
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · exact Or.inr ((repairedStoppingGraph.mem_neighborFinset q p).mp hp)

/-- The finite closed graph neighborhood covers the centered threefold
enlargement of a refined stopping cell. -/
theorem refinedStoppingCell_enlargement_subset_iUnion_closedNeighbors
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (q : RefinedStoppingCell failure omega base) :
    translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q) ⊆
      ⋃ p ∈ repairedStoppingClosedNeighbors q,
        translatedCube d (refinedStoppingScale p) (refinedStoppingCenter p) := by
  intro x hx
  have hcover := iUnion_refinedStoppingCell_eq_univ
    failure omega hinitial hrepair
  have hxAll : x ∈ ⋃ p : RefinedStoppingCell failure omega base,
      translatedCube d (refinedStoppingScale p) (refinedStoppingCenter p) := by
    rw [hcover]
    trivial
  obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxAll
  have hp : p ∈ repairedStoppingClosedNeighbors q := by
    by_cases hpq : p = q
    · rw [hpq]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        ((repairedStoppingGraph.mem_neighborFinset q p).mpr
          (repairedStoppingGraph_adj_of_meets_enlargement (Ne.symm hpq)
            ⟨x, hx, hxp⟩))
  exact Set.mem_iUnion₂.mpr ⟨p, hp, hxp⟩

/-- The family of refined centered enlargements is locally finite whenever
the repaired cover exists. -/
theorem locallyFinite_refinedStoppingCell_enlargements
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1) :
    LocallyFinite fun q : RefinedStoppingCell failure omega base ↦
      translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q) := by
  intro x
  have hcover := iUnion_refinedStoppingCell_eq_univ
    failure omega hinitial hrepair
  have hxAll : x ∈ ⋃ p : RefinedStoppingCell failure omega base,
      translatedCube d (refinedStoppingScale p) (refinedStoppingCenter p) := by
    rw [hcover]
    trivial
  obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxAll
  let t := translatedCube d (refinedStoppingScale p) (refinedStoppingCenter p)
  refine ⟨t, ?_, ?_⟩
  · dsimp only [t]
    rw [translatedCube_eq_metricBall] at hxp ⊢
    exact Metric.isOpen_ball.mem_nhds hxp
  · refine (repairedStoppingClosedNeighbors p).finite_toSet.subset ?_
    intro q hq
    have hinter :
        (translatedCube d (refinedStoppingScale q + 1)
            (refinedStoppingCenter q) ∩
          translatedCube d (refinedStoppingScale p)
            (refinedStoppingCenter p)).Nonempty := by
      simpa only [t, mem_ofPred_eq] using hq
    by_cases hqp : q = p
    · rw [hqp]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        ((repairedStoppingGraph.mem_neighborFinset p q).mpr
          (repairedStoppingGraph_adj_of_meets_enlargement hqp hinter).symm)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
