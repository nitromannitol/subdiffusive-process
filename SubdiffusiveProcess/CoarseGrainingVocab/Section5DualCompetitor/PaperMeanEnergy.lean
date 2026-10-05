module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepConcreteCellCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannFlux

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Gradient-energy form of the paper-sign dual constant-cell readout.  Mirror
of `oneStepSelectedNeumannMean_gradientEnergy_eq_randomAStarMatrix_inv` with
the manuscript-sign mean field and a free cutoff index. -/
theorem oneStepSelectedPaperNeumannMean_gradientEnergy_eq_randomAStarMatrix_inv
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h L : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : Sample d) (hh : 0 < h)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)))
    (hR : R ∈ descendantsAtDepth Q j) :
    let P := fun S ↦ oneStepPaperNeumannCellMeanField M n h q Q S omega hh
    let X := oneStepSelectedNeumannCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))
      P hEll
      (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
        M n h q Q omega hh) R hR
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.potential.toH1Function.grad x)
          (matVecMul
            (scalarCoeffField
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)
            (X.potential.toH1Function.grad x))) =
      vecDot (oneStepPaperNeumannCellSlope M n h q Q R omega hh)
        (matVecMul ((randomAStarMatrix M L
          (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹)
          (oneStepPaperNeumannCellSlope M n h q Q R omega hh)) := by
  dsimp only
  let a := scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
  let X := oneStepSelectedNeumannCell a
    (fun S ↦ oneStepPaperNeumannCellMeanField M n h q Q S omega hh)
    hEll
    (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
      M n h q Q omega hh) R hR
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hvol : 0 < (volume (openCubeSet R)).toReal := by
    simpa [volume_openCubeSet_toReal] using cubeVolume_pos R
  obtain ⟨recovery, _sigma0, compat, _hA, _hSInv, hS, _hK, _hSigma,
      _hcanonical⟩ :=
    Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet R) (hEll R hR) hvol
  have henergy := X.energy_eq_vecDot_sigmaStarInvCoarse
    (fun x ↦ scalarMatrix_isSymm _) (hEll R hR) hS
  rw [randomAStarMatrix_inv_eq_sigmaStarInvCoarse M L omega R]
  calc
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.potential.toH1Function.grad x)
          (matVecMul (a x) (X.potential.toH1Function.grad x))) =
        volumeAverage (openCubeSet R)
          (scalarVariationEnergyIntegrand a
            (X.isConstantFluxNeumannSolution (hEll R hR)
              ).toAHarmonicFunction) := by
      congr 1
      funext x
      simp only [scalarVariationEnergyIntegrand,
        IsConstantFluxNeumannSolution.toAHarmonicFunction_grad]
      rw [show symmPart (a x) = a x by
        simp only [a, scalarCoeffField,
          Homogenization.Book.Ch02.symmPart_scalarMatrix]]
    _ = _ := by
      simpa only [X, a, oneStepPaperNeumannCellMeanField,
        oneStepPaperNeumannCellSlope, oneStepCellMeanVec] using! henergy

/-- Flux-energy form of the paper-sign dual constant-cell readout, in the
inverse-star metric `(blockMatrixOfCoeff _).lowerRight` that the glued
competitor's energy density uses. -/
theorem oneStepSelectedPaperNeumannMean_energy_eq_randomAStarMatrix_inv
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h L : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : Sample d) (hh : 0 < h)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)))
    (hR : R ∈ descendantsAtDepth Q j) :
    let P := fun S ↦ oneStepPaperNeumannCellMeanField M n h q Q S omega hh
    let X := oneStepSelectedNeumannCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))
      P hEll
      (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
        M n h q Q omega hh) R hR
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x)
          (matVecMul
            ((blockMatrixOfCoeff
              (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)).lowerRight)
            (X.flux x))) =
      vecDot (oneStepPaperNeumannCellSlope M n h q Q R omega hh)
        (matVecMul ((randomAStarMatrix M L
          (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹)
          (oneStepPaperNeumannCellSlope M n h q Q R omega hh)) := by
  dsimp only
  let a := scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
  let X := oneStepSelectedNeumannCell a
    (fun S ↦ oneStepPaperNeumannCellMeanField M n h q Q S omega hh)
    hEll
    (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
      M n h q Q omega hh) R hR
  have hfluxEnergy (x : Vec d) :
      vecDot (X.flux x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (X.flux x)) =
        vecDot (X.potential.toH1Function.grad x)
          (matVecMul (a x) (X.potential.toH1Function.grad x)) := by
    have hdet : IsUnit (a x).det :=
      isUnit_det_of_isEllipticMatrix
        (isEllipticMatrix_scalarMatrix
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x))
    have haSymm : symmPart (a x) = a x := by
      simp only [a, scalarCoeffField,
        Homogenization.Book.Ch02.symmPart_scalarMatrix]
    unfold OneStepNeumannCellMinimizer.flux blockMatrixOfCoeff
    dsimp only
    rw [haSymm, matVecMul_mul, Matrix.nonsing_inv_mul (a x) hdet,
      matVecMul_one]
    exact vecDot_comm _ _
  calc
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (X.flux x))) =
        volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.potential.toH1Function.grad x)
            (matVecMul (a x) (X.potential.toH1Function.grad x))) := by
      congr 1
      funext x
      exact hfluxEnergy x
    _ = _ :=
      oneStepSelectedPaperNeumannMean_gradientEnergy_eq_randomAStarMatrix_inv
        M n h L q Q R omega hh hEll hR

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
