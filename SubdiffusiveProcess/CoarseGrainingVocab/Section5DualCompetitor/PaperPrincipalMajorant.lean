module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.CutoffRatio
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.DualPrincipalMajorant

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- **The principal cell domination.**  The high-cutoff inverse-star energy of
the glued competitor's principal cell is bounded by the manuscript-sign
principal envelope. -/
theorem volumeAverage_paperPrincipalCell_energy_le_majorant
    {d j K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (R : Homogenization.TriadicCube d)
    (omega : Sample d) (hh : 0 < h)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : ∀ S ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      IsEllipticFieldOn lamLow LamLow (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)))
    (hHigh : ∀ S ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      IsEllipticFieldOn lamHigh LamHigh (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)))
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot ((oneStepSelectedNeumannCell
            (scalarCoeffField
              (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))
            (fun S ↦ oneStepPaperNeumannCellMeanField M n h q
              (originCube d (K : ℤ)) S omega hh) hHigh
            (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
              M n h q (originCube d (K : ℤ)) omega hh) R hR).flux x)
          (matVecMul ((blockMatrixOfCoeff
            (scalarCoeffField
              (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega) x)).lowerRight)
            ((oneStepSelectedNeumannCell
              (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))
              (fun S ↦ oneStepPaperNeumannCellMeanField M n h q
                (originCube d (K : ℤ)) S omega hh) hHigh
              (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
                M n h q (originCube d (K : ℤ)) omega hh) R hR).flux x))) ≤
      oneStepDualPrincipalMajorant (K := K) M n h q R omega hh := by
  have hidentity :=
    oneStepSelectedPaperNeumannMean_energy_eq_randomAStarMatrix_inv
      M n h (n + h) q (originCube d (K : ℤ)) R omega hh hHigh hR
  have hratio := vecDot_randomAStarInv_high_le_lowerSourceCellWeight_mul
    M n h omega R (oneStepPaperNeumannCellSlope M n h q
      (originCube d (K : ℤ)) R omega hh) (hLow R hR) (hHigh R hR)
  exact hidentity.trans_le hratio

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
