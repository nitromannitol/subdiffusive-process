module

public import SubdiffusiveProcess.Geometry.CoordinateFold
public import SubdiffusiveProcess.CoarseGrainingVocab.Model
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging

@[expose] public section

open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

namespace SubdiffusiveProcess

/-- Every literal coordinate fold of a finite GMC cutoff has the coherent scalar coefficient data used by the imported coarse-graining estimates. -/
theorem nonempty_foldedACutoffTriadicData {d : ℕ}
    (M : GMCModel d) (L : ℕ) (ω : PotentialSample d)
    (z : SpatialCoordinates d) (I P : Finset (Fin d)) :
    Nonempty (ScalarTriadicCoeffData
      (fun x => aCutoff M L ω (coordinateFold z I P x))) := by
  refine ⟨{ onCube := fun Q => ?_ }⟩
  exact Classical.choice
    (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
      ((continuous_aCutoff M L ω).comp (coordinateFold_continuous z I P))
      (fun x => aCutoff_pos M L ω (coordinateFold z I P x))
      (Homogenization.Book.Ch02.cubeDomain Q))

end SubdiffusiveProcess
