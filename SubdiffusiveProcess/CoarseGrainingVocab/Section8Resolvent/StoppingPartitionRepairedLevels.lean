import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedNeighbourCover
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionSphereGrowth

/-!
# Finite graph levels for the repaired stopping family

Finite graph balls are constructed recursively from neighbor finsets.  Exact
distance spheres are filters of those balls, so no finiteness hypothesis on a
set comprehension is required.  The repaired degree bound then gives the
geometric sphere growth consumed by the exterior row.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Cell : Type*} [DecidableEq Cell]

/-- Vertices reachable from a finite source in at most `j` recursive graph
steps. -/
def stoppingGraphReachBall (G : SimpleGraph Cell) [G.LocallyFinite]
    (source : Finset Cell) : ℕ → Finset Cell
  | 0 => source
  | j + 1 => stoppingGraphReachBall G source j ∪
      (stoppingGraphReachBall G source j).biUnion fun q ↦ G.neighborFinset q

/-- A vertex at exact source distance `j` belongs to the recursive radius-`j`
graph ball. -/
theorem mem_stoppingGraphReachBall_of_distance_eq
    (G : SimpleGraph Cell) [G.LocallyFinite] (hconnected : G.Connected)
    {source : Finset Cell} (hsource : source.Nonempty) :
    ∀ {j q}, stoppingGraphDistance G source hsource q = j →
      q ∈ stoppingGraphReachBall G source j := by
  intro j
  induction j with
  | zero =>
      intro q hq
      obtain ⟨s, hs, hqs⟩ :=
        exists_source_dist_eq_stoppingGraphDistance G hsource q
      have hdist : G.dist q s = 0 := hqs.trans hq
      have hqsEq : q = s := hconnected.dist_eq_zero_iff.mp hdist
      subst s
      exact hs
  | succ j ih =>
      intro q hq
      obtain ⟨p, hqp, hp⟩ :=
        exists_adj_stoppingGraphDistance_eq_pred G hconnected hsource hq
      have hpBall : p ∈ stoppingGraphReachBall G source j := ih hp
      rw [stoppingGraphReachBall, Finset.mem_union]
      exact Or.inr (Finset.mem_biUnion.mpr
        ⟨p, hpBall, (G.mem_neighborFinset p q).mpr hqp.symm⟩)

/-- The finite exact-distance sphere around a finite source. -/
def stoppingGraphLevelCells (G : SimpleGraph Cell) [G.LocallyFinite]
    (source : Finset Cell) (hsource : source.Nonempty) (j : ℕ) :
    Finset Cell :=
  (stoppingGraphReachBall G source j).filter fun q ↦
    stoppingGraphDistance G source hsource q = j

@[simp]
theorem mem_stoppingGraphLevelCells_iff
    (G : SimpleGraph Cell) [G.LocallyFinite] (hconnected : G.Connected)
    {source : Finset Cell} (hsource : source.Nonempty) (j : ℕ) (q : Cell) :
    q ∈ stoppingGraphLevelCells G source hsource j ↔
      stoppingGraphDistance G source hsource q = j := by
  rw [stoppingGraphLevelCells, Finset.mem_filter]
  exact and_iff_right_of_imp
    (mem_stoppingGraphReachBall_of_distance_eq G hconnected hsource)

/-- Uniform degree bounds give geometric growth of the canonical exact
distance spheres. -/
theorem card_stoppingGraphLevelCells_le_degree_pow
    (G : SimpleGraph Cell) [G.LocallyFinite] (hconnected : G.Connected)
    {source : Finset Cell} (hsource : source.Nonempty) {D : ℕ}
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D) :
    ∀ j, (stoppingGraphLevelCells G source hsource j).card ≤
      (stoppingGraphLevelCells G source hsource 0).card * D ^ j :=
  card_stoppingLevelCells_le_degree_pow G hconnected hsource
    (stoppingGraphLevelCells G source hsource)
    (mem_stoppingGraphLevelCells_iff G hconnected hsource) le_rfl hdegree

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- The exact repaired-graph levels satisfy the explicit dimension-only
sphere-growth bound. -/
theorem card_repairedStoppingGraphLevelCells_le
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    {source : Finset (RefinedStoppingCell failure omega base)}
    (hsource : source.Nonempty) :
    ∀ j,
      (stoppingGraphLevelCells repairedStoppingGraph source hsource j).card ≤
        (stoppingGraphLevelCells repairedStoppingGraph source hsource 0).card *
          repairedStoppingDegreeBound d ^ j :=
  card_stoppingGraphLevelCells_le_degree_pow repairedStoppingGraph
    (repairedStoppingGraph_connected failure omega hinitial hrepair) hsource
    card_repairedStoppingGraph_neighborFinset_le

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
