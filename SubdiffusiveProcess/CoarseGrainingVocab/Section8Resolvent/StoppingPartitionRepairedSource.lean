import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedNeighbourCover
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionSourceCells




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- The finite repaired-cell source family whose centered enlargements meet a
fixed closed ball. -/
def repairedStoppingSourceCells
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) (R : ℝ) :
    Finset (RefinedStoppingCell failure omega base) :=
  stoppingSourceCells
    (fun q ↦ translatedCube d (refinedStoppingScale q + 1)
      (refinedStoppingCenter q))
    (locallyFinite_refinedStoppingCell_enlargements hinitial hrepair) x0 R

theorem mem_repairedStoppingSourceCells_iff
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) (R : ℝ) (q : RefinedStoppingCell failure omega base) :
    q ∈ repairedStoppingSourceCells hinitial hrepair x0 R ↔
      (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q) ∩ Metric.closedBall x0 R).Nonempty := by
  exact mem_stoppingSourceCells_iff
    (fun q ↦ translatedCube d (refinedStoppingScale q + 1)
      (refinedStoppingCenter q))
    (locallyFinite_refinedStoppingCell_enlargements hinitial hrepair) x0 R q

/-- The repaired source family is nonempty for every nonnegative source
radius. -/
theorem repairedStoppingSourceCells_nonempty
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    (repairedStoppingSourceCells hinitial hrepair x0 R).Nonempty := by
  apply stoppingSourceCells_translatedCube_nonempty
    (fun q : RefinedStoppingCell failure omega base ↦ refinedStoppingScale q)
    (fun q ↦ refinedStoppingCenter q)
    (locallyFinite_refinedStoppingCell_enlargements hinitial hrepair)
  · intro x
    have hcover := iUnion_refinedStoppingCell_eq_univ
      failure omega hinitial hrepair
    have hx : x ∈ ⋃ q : RefinedStoppingCell failure omega base,
        translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) := by
      rw [hcover]
      trivial
    exact Set.mem_iUnion.mp hx
  · exact hR

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
