module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionMassContractionConsumer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedGraphDistance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedLevels
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedSource

@[expose] public section

/-!
# Repaired stopping partition composition to the mesoscopic exterior row

This module discharges every geometric premise of
`wholeSpaceSolution_exterior_decay_of_cell_mass_contractions` for the repaired
half-grid stopping family.  The only remaining assumptions are the source-cell
mass bound, the per-cell mass contractions, and the numerical contraction
condition.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open _root_.SubdiffusiveProcess.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

omit [NeZero d] in
/-- The repaired degree bound is strictly positive. -/
theorem repairedStoppingDegreeBound_pos : 0 < repairedStoppingDegreeBound d := by
  unfold repairedStoppingDegreeBound
  positivity

/-- **Exterior decay on the repaired stopping partition.**

The graph levels are the canonical finite exact-distance spheres.  Closed
graph neighborhoods cover every centered enlargement and have at most
`D(d)+1` members.  The repaired degree bound controls sphere growth, while
absence of a short crossing gives the exterior cover at the required graph
distance. -/
theorem wholeSpaceSolution_exterior_decay_of_repaired_stopping_cells
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsourceNonempty : source.Nonempty) (x0 : Vec d) (R epsilon : ℝ) (k : ℕ)
    (hgood : ¬ RepairedStoppingShortCrossing source hsourceNonempty
      x0 R epsilon k)
    {A theta0 : ℝ} (hA : 0 ≤ A) (htheta0 : 0 < theta0)
    (heffective :
      (repairedStoppingDegreeBound d : ℝ) *
        (((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) * theta0) < 1)
    (hsource : ∀ q,
      stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q = 0 →
        ∫ x in translatedCube d (refinedStoppingScale q)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤ A)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
        ∫ x in translatedCube d (refinedStoppingScale q)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
        theta0 * ∫ x in translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume) :
    ∫ x in (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ, u.toFun x ^ 2 ∂volume ≤
      ((stoppingGraphLevelCells repairedStoppingGraph source
          hsourceNonempty 0).card : ℝ) * A *
        (1 - (repairedStoppingDegreeBound d : ℝ) *
          (((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) * theta0))⁻¹ *
        Real.exp
          (Real.log ((repairedStoppingDegreeBound d : ℝ) *
            (((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) * theta0)) *
            (epsilon * (3 : ℝ) ^ k)) := by
  let levelCells : ℕ → Finset (RefinedStoppingCell failure omega base) :=
    stoppingGraphLevelCells repairedStoppingGraph source hsourceNonempty
  have hconnected := repairedStoppingGraph_connected failure omega hinitial hrepair
  refine wholeSpaceSolution_exterior_decay_of_graph_cell_mass_contractions u
    repairedStoppingGraph source hsourceNonempty levelCells
    (fun j q ↦ mem_stoppingGraphLevelCells_iff repairedStoppingGraph
      hconnected hsourceNonempty j q)
    refinedStoppingScale refinedStoppingCenter
    ((Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ)
    (levelCells 0).card (repairedStoppingDegreeBound d)
    (repairedStoppingDegreeBound d + 1) hA htheta0 (by omega)
    repairedStoppingDegreeBound_pos heffective hsource hcell ?_ ?_ ?_
  · intro q _
    refine ⟨repairedStoppingClosedNeighbors q,
      repairedStoppingClosedNeighbors_nonempty q,
      card_repairedStoppingClosedNeighbors_le q, ?_,
      refinedStoppingCell_enlargement_subset_iUnion_closedNeighbors
        hinitial hrepair q⟩
    intro p hp
    rcases eq_or_adj_of_mem_repairedStoppingClosedNeighbors hp with rfl | hp
    · omega
    · exact repairedStoppingGraphDistance_le_succ_of_adj
        hinitial hrepair source hsourceNonempty hp
  · intro j
    exact card_repairedStoppingGraphLevelCells_le hinitial hrepair
      hsourceNonempty j
  · intro x hx
    have hcover := iUnion_refinedStoppingCell_eq_univ
      failure omega hinitial hrepair
    have hxAll : x ∈ ⋃ q : RefinedStoppingCell failure omega base,
        translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) := by
      rw [hcover]
      trivial
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxAll
    refine ⟨q, ?_, hxq⟩
    exact natCeil_le_repairedStoppingGraphDistance_of_not_shortCrossing source
      hsourceNonempty x0 R epsilon hgood ⟨x, hxq, hx⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
