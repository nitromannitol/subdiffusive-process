module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszStoppingGeneric
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionHalfGridRefinement

@[expose] public section

/-!
# Composition from the repaired half-grid carrier to the flux-row partition

This file instantiates the generic flux-row geometry with agent1's concrete
carrier `RefinedStoppingCell`.  The repaired graph remains an explicit input;
all carrier, failure-event, scale, centre, and cover fields are discharged.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- The smooth subordinate partition of unity on the repaired half-grid
cells, in the shape the flux-row carrier consumes. -/
abbrev RepairedStoppingCutoff [NeZero d] (failure : TriadicCube d → Set Omega)
    (omega : Omega) (base : ℤ) :=
  StoppingFluxRowCutoff d (RefinedStoppingCell failure omega base)
    refinedStoppingScale refinedStoppingCenter

/-- The concrete repaired half-grid cells form a generic stopping family as
soon as their repaired intersection graph and its degree bound are supplied. -/
def FluxRowRieszStoppingFamily.ofRefinedStoppingCells
    [NeZero d] (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (G : SimpleGraph (RefinedStoppingCell failure omega base))
    [G.LocallyFinite] (D : ℕ)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D)
    (hintersection : ∀ {q p}, q ≠ p →
      (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p + 1)
          (refinedStoppingCenter p)).Nonempty → G.Adj q p)
    (chi : RepairedStoppingCutoff failure omega base) :
    FluxRowRieszStoppingFamily (Cell := RefinedStoppingCell failure omega base)
      failure omega :=
  FluxRowRieszStoppingFamily.ofBoundedDegree failure omega
    refinedStoppingFailureCube refinedStoppingScale
    refinedStoppingScale_eq_failureCube refinedStoppingCenter
    (iUnion_refinedStoppingCell_eq_univ failure omega hinitial hrepair)
    chi G D hdegree hintersection

@[simp]
theorem FluxRowRieszStoppingFamily.ofRefinedStoppingCells_failureCube
    [NeZero d] (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (G : SimpleGraph (RefinedStoppingCell failure omega base))
    [G.LocallyFinite] (D : ℕ)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D)
    (hintersection : ∀ {q p}, q ≠ p →
      (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p + 1)
          (refinedStoppingCenter p)).Nonempty → G.Adj q p)
    (chi : RepairedStoppingCutoff failure omega base)
    (q : RefinedStoppingCell failure omega base) :
    (FluxRowRieszStoppingFamily.ofRefinedStoppingCells failure omega hinitial
      hrepair G D hdegree hintersection chi).failureCube q =
      refinedStoppingFailureCube q :=
  rfl

@[simp]
theorem FluxRowRieszStoppingFamily.ofRefinedStoppingCells_toPartition_cell
    [NeZero d] (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (G : SimpleGraph (RefinedStoppingCell failure omega base))
    [G.LocallyFinite] (D : ℕ)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D)
    (hintersection : ∀ {q p}, q ≠ p →
      (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p + 1)
          (refinedStoppingCenter p)).Nonempty → G.Adj q p)
    (chi : RepairedStoppingCutoff failure omega base)
    (q : RefinedStoppingCell failure omega base) :
    (FluxRowRieszStoppingFamily.ofRefinedStoppingCells failure omega hinitial
      hrepair G D hdegree hintersection chi).toPartition.cell q =
      translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q) :=
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
