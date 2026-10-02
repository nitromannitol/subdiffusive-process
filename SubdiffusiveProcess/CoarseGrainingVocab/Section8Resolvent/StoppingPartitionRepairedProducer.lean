import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszStoppingRefined
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedGraph




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}

/-- The repaired selected cells, equipped with their bounded-degree
intersection graph, give the generic stopping family required by the flux
row. -/
def repairedFluxRowRieszStoppingFamily
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base) :
    FluxRowRieszStoppingFamily
      (Cell := RefinedStoppingCell failure omega base) failure omega :=
  FluxRowRieszStoppingFamily.ofRefinedStoppingCells failure omega hinitial
    hrepair repairedStoppingGraph (repairedStoppingDegreeBound d)
    card_repairedStoppingGraph_neighborFinset_le
    repairedStoppingGraph_adj_of_enlargements_inter_nonempty chi

@[simp]
theorem repairedFluxRowRieszStoppingFamily_failureCube
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (q : RefinedStoppingCell failure omega base) :
    (repairedFluxRowRieszStoppingFamily failure omega hinitial hrepair
        chi).failureCube
        q = refinedStoppingFailureCube q :=
  rfl

@[simp]
theorem repairedFluxRowRieszStoppingFamily_graph
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base) :
    (repairedFluxRowRieszStoppingFamily failure omega hinitial hrepair chi).graph =
      repairedStoppingGraph :=
  rfl

@[simp]
theorem repairedFluxRowRieszStoppingFamily_degreeBound
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base) :
    (repairedFluxRowRieszStoppingFamily failure omega hinitial hrepair
        chi).degreeBound =
      repairedStoppingDegreeBound d :=
  rfl

/-- Every produced cell inherits any coefficient or regularity property that
is implied by non-failure of its selected triadic ancestor. -/
theorem repairedFluxRowRieszStoppingFamily_property_of_not_mem_failure
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (Good : TriadicCube d → Prop)
    (hgood : ∀ Q, omega ∉ failure Q → Good Q)
    (q : RefinedStoppingCell failure omega base) :
    Good ((repairedFluxRowRieszStoppingFamily failure omega hinitial
      hrepair chi).failureCube q) := by
  rw [repairedFluxRowRieszStoppingFamily_failureCube]
  exact refinedStoppingCell_property_of_not_mem_failure failure hfinite Good
    hgood q

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
