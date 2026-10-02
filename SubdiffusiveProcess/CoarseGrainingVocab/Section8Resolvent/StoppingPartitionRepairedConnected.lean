import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionIntersectionGraphConnected




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}

/-- The bounded-degree graph produced from the repaired half-grid cover is
connected. -/
theorem repairedStoppingGraph_connected
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1) :
    (repairedStoppingGraph (failure := failure) (omega := omega)
      (base := base)).Connected := by
  let cell : RefinedStoppingCell failure omega base → Set (Vec d) :=
    fun q ↦ translatedCube d (refinedStoppingScale q)
      (refinedStoppingCenter q)
  have hcover : (⋃ q, cell q) = (Set.univ : Set (Vec d)) := by
    exact iUnion_refinedStoppingCell_eq_univ failure omega hinitial hrepair
  have hzero : (0 : Vec d) ∈ ⋃ q, cell q := by
    rw [hcover]
    trivial
  obtain ⟨q0, _⟩ := Set.mem_iUnion.mp hzero
  letI : Nonempty (RefinedStoppingCell failure omega base) := ⟨q0⟩
  apply simpleGraph_connected_of_open_cover_of_intersection_edge cell
  · intro q
    dsimp only [cell]
    rw [translatedCube_eq_metricBall]
    exact Metric.isOpen_ball
  · intro q
    refine ⟨refinedStoppingCenter q, ?_⟩
    dsimp only [cell]
    rw [translatedCube_eq_metricBall]
    exact Metric.mem_ball_self (by positivity)
  · exact hcover
  · intro q p hne hinter
    exact repairedStoppingGraph_adj_of_inter_nonempty hne hinter

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
