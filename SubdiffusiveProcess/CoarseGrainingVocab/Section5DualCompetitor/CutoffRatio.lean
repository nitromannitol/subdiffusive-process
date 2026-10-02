import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.PaperMeanEnergy




open MeasureTheory Homogenization Homogenization.Book

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-- Pointwise: the inverse-star energy density of a cell minimizer's flux is
its coefficient energy density. -/
theorem vecDot_flux_lowerRight_eq_gradientEnergy
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    {R : TriadicCube d} {G : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer R
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) G)
    (x : Vec d) :
    vecDot (X.flux x)
        (matVecMul ((blockMatrixOfCoeff
          (scalarCoeffField
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
          (X.flux x)) =
      vecDot (X.potential.toH1Function.grad x)
        (matVecMul
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
          (X.potential.toH1Function.grad x)) := by
  set a := scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) with ha
  have hdet : IsUnit (a x).det :=
    isUnit_det_of_isEllipticMatrix
      (isEllipticMatrix_scalarMatrix
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x))
  have haSymm : symmPart (a x) = a x := by
    simp only [ha, scalarCoeffField,
      Homogenization.Book.Ch02.symmPart_scalarMatrix]
  unfold OneStepNeumannCellMinimizer.flux blockMatrixOfCoeff
  dsimp only
  rw [haSymm, matVecMul_mul, Matrix.nonsing_inv_mul (a x) hdet,
    matVecMul_one]
  exact vecDot_comm _ _

/-- **Constant-datum dual cell readout, gradient form.**  For an arbitrary
constant flux datum `v`, the coefficient energy of the corresponding cell
minimizer is exactly the random inverse-star quadratic form at the same
cutoff. -/
theorem volumeAverage_neumannConstMinimizer_gradientEnergy_eq_randomAStarInv
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    (R : TriadicCube d) (v : Vec d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)))
    (X : OneStepNeumannCellMinimizer R
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))
      (fun _ ↦ v)) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.potential.toH1Function.grad x)
          (matVecMul
            (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
            (X.potential.toH1Function.grad x))) =
      vecDot v (matVecMul ((randomAStarMatrix M L
        (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹) v) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hvol : 0 < (volume (openCubeSet R)).toReal := by
    simpa [volume_openCubeSet_toReal] using cubeVolume_pos R
  obtain ⟨recovery, _sigma0, compat, _hA, _hSInv, hS, _hK, _hSigma,
      _hcanonical⟩ :=
    Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet R) hEll hvol
  have henergy := X.energy_eq_vecDot_sigmaStarInvCoarse
    (fun x ↦ scalarMatrix_isSymm _) hEll hS
  rw [randomAStarMatrix_inv_eq_sigmaStarInvCoarse M L omega R]
  refine Eq.trans ?_ henergy
  congr 1
  funext x
  simp only [scalarVariationEnergyIntegrand,
    IsConstantFluxNeumannSolution.toAHarmonicFunction_grad,
    scalarCoeffField, Homogenization.Book.Ch02.symmPart_scalarMatrix]

/-- Flux form of the constant-datum dual cell readout, in the inverse-star
metric that the glued competitor's energy density uses. -/
theorem volumeAverage_neumannConstMinimizer_inverseEnergy_eq_randomAStarInv
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    (R : TriadicCube d) (v : Vec d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)))
    (X : OneStepNeumannCellMinimizer R
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))
      (fun _ ↦ v)) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x)
          (matVecMul ((blockMatrixOfCoeff
            (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
            (X.flux x))) =
      vecDot v (matVecMul ((randomAStarMatrix M L
        (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹) v) := by
  rw [show (fun x ↦ vecDot (X.flux x)
        (matVecMul ((blockMatrixOfCoeff
          (scalarCoeffField
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
          (X.flux x))) =
      fun x ↦ vecDot (X.potential.toH1Function.grad x)
        (matVecMul
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
          (X.potential.toH1Function.grad x)) from
    funext fun x ↦ vecDot_flux_lowerRight_eq_gradientEnergy M L omega X x]
  exact volumeAverage_neumannConstMinimizer_gradientEnergy_eq_randomAStarInv
    M L omega R v hEll X

/-- **Cell-level starred variational principle at a cutoff coefficient.**
Specialization of `vecDot_sigmaStarInvCoarse_le_volumeAverage_lowerRight_energy`
to `aCutoff`, with the two side conditions discharged. -/
theorem vecDot_randomAStarInv_le_volumeAverage_lowerRight_energy
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    (R : TriadicCube d) (v : Vec d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)))
    (g : Vec d → Vec d) (hg : MemVectorL2 (openCubeSet R) g)
    (hgSol : IsSolenoidalZeroNormalTraceOn (openCubeSet R)
      (fun x ↦ g x - v)) :
    vecDot v (matVecMul ((randomAStarMatrix M L
        (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹) v) ≤
      volumeAverage (openCubeSet R) (fun x ↦
        vecDot (g x)
          (matVecMul ((blockMatrixOfCoeff
            (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
            (g x))) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hvol : 0 < (volume (openCubeSet R)).toReal := by
    simpa [volume_openCubeSet_toReal] using cubeVolume_pos R
  rw [randomAStarMatrix_inv_eq_sigmaStarInvCoarse M L omega R]
  exact vecDot_sigmaStarInvCoarse_le_volumeAverage_lowerRight_energy
    (isOpenBoundedConvexDomain_openCubeSet R).isSobolevRegularDomain hEll
    ⟨_, isCoarseBlockMatrix_ch02_aCutoff M L omega R⟩ hvol.ne'
    (mu_zero_right_eq_responseJ_aCutoff M L omega R) v g hg hgSol

/-- **Cutoff transfer for the dual cell readout.**  The high-cutoff random
inverse-star quadratic form is dominated by the reciprocal fresh-cutoff weight
times the low-cutoff one, uniformly in the constant datum. -/
theorem vecDot_randomAStarInv_high_le_lowerSourceCellWeight_mul
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (omega : Sample d)
    (R : TriadicCube d) (v : Vec d)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : IsEllipticFieldOn lamLow LamLow (openCubeSet R)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)))
    (hHigh : IsEllipticFieldOn lamHigh LamHigh (openCubeSet R)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))) :
    vecDot v (matVecMul ((randomAStarMatrix M (n + h)
        (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹) v) ≤
      oneStepLowerSourceCellWeight M n h R omega *
        vecDot v (matVecMul ((randomAStarMatrix M n
          (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹) v) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  set aLow := scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
    with haLow
  let X : OneStepNeumannCellMinimizer R aLow (fun _ ↦ v) :=
    oneStepNeumannCellMinimizer R hLow (fun _ ↦ v) (memVectorL2_const v)
  have hfluxL2 : MemVectorL2 (openCubeSet R) X.flux :=
    X.flux_memVectorL2 hLow
  have hresidual : IsSolenoidalZeroNormalTraceOn (openCubeSet R)
      (fun x ↦ X.flux x - v) :=
    X.residual_zeroNormalTrace hLow (MeasureTheory.memLp_const v)
  have hstep1 := vecDot_randomAStarInv_le_volumeAverage_lowerRight_energy
    M (n + h) omega R v hHigh X.flux hfluxL2 hresidual
  have hratio := volumeAverage_cutoff_flux_inverseEnergy_le_ratioSup_mul
    M n (n + h) (Homogenization.Book.Ch02.cubeDomain R) omega
      X.potential.toH1Function.grad
      X.potential.toH1Function.grad_memVectorL2 hLow hHigh
  have hlow :=
    volumeAverage_neumannConstMinimizer_gradientEnergy_eq_randomAStarInv
      M n omega R v hLow X
  have hratio' :
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.flux x)
            (matVecMul ((blockMatrixOfCoeff
              (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega)
                x)).lowerRight)
              (X.flux x))) ≤
        oneStepLowerSourceCellWeight M n h R omega *
          volumeAverage (openCubeSet R) (fun x ↦
            vecDot (X.potential.toH1Function.grad x)
              (matVecMul (aLow x) (X.potential.toH1Function.grad x))) := by
    simpa only [X, haLow, blockMatrixOfCoeff,
      OneStepNeumannCellMinimizer.flux, oneStepLowerSourceCellWeight,
      Homogenization.Book.Ch02.cubeDomain_coe] using hratio
  exact hstep1.trans (hratio'.trans_eq (by rw [hlow]))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
