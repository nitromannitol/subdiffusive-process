module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFluxGreedyColor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFluxInterface

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization

noncomputable section

variable {d : ℕ} {Cell : Type*} [Encodable Cell] [DecidableEq Cell]

/-- Instantiate the flux-row partition using the same bounded-degree graph
which controls stopping-graph sphere growth. -/
def stoppingFluxRowRieszPartitionOfBoundedDegree
    (scale : Cell → ℤ) (center : Cell → Vec d)
    (hcover : (⋃ q, translatedCube d (scale q) (center q)) = Set.univ)
    (G : SimpleGraph Cell) [G.LocallyFinite] (D : ℕ)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D)
    (hintersection : ∀ {q p}, q ≠ p →
      (translatedCube d (scale q + 1) (center q) ∩
        translatedCube d (scale p + 1) (center p)).Nonempty → G.Adj q p)
    (chi : StoppingFluxRowCutoff d Cell scale center) :
    FluxRowRieszPartition d Cell :=
  stoppingFluxRowRieszPartition scale center hcover (D + 1) (by omega) G
    (stoppingBoundedDegreeColoring G D hdegree) hintersection chi

@[simp]
theorem stoppingFluxRowRieszPartitionOfBoundedDegree_overlapCount
    (scale : Cell → ℤ) (center : Cell → Vec d)
    (hcover : (⋃ q, translatedCube d (scale q) (center q)) = Set.univ)
    (G : SimpleGraph Cell) [G.LocallyFinite] (D : ℕ)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D)
    (hintersection : ∀ {q p}, q ≠ p →
      (translatedCube d (scale q + 1) (center q) ∩
        translatedCube d (scale p + 1) (center p)).Nonempty → G.Adj q p)
    (chi : StoppingFluxRowCutoff d Cell scale center) :
    (stoppingFluxRowRieszPartitionOfBoundedDegree scale center hcover G D
      hdegree hintersection chi).overlapCount = D + 1 :=
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
