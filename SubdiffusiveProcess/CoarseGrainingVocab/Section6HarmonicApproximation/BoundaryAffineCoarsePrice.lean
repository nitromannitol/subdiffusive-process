module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLocalizedCellMinimizers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergy

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch02 Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem localized_energy_eq_two_mul_symmetricDirichletEnergy
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) u =
      2 * symmetricDirichletEnergyValue (cubeDomain Q)
        ((aCutoffFamily M L omega).coeffOn Q) u := by
  unfold localizedCoeffEnergyValue symmetricDirichletEnergyValue
  unfold normalizedSetAverage Ch02.average volumeAverage
  simp only [Ch02.cubeDomain_coe]
  rw [show 2 * ((volume (openCubeSet Q)).toReal⁻¹ *
      ∫ x in openCubeSet Q,
        (1 / 2 : ℝ) * vecDot (u.grad x)
          (matVecMul (((aCutoffFamily M L omega).coeffOn Q).toCoeffField x)
            (u.grad x)) ∂volume) =
      (volume (openCubeSet Q)).toReal⁻¹ *
        (2 * ∫ x in openCubeSet Q,
          (1 / 2 : ℝ) * vecDot (u.grad x)
            (matVecMul (((aCutoffFamily M L omega).coeffOn Q).toCoeffField x)
              (u.grad x)) ∂volume) by ring]
  apply congrArg (fun r : ℝ => (volume (openCubeSet Q)).toReal⁻¹ * r)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField]
  have hsymm : symmPart (scalarMatrix (d := d)
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)) =
      scalarMatrix (d := d) (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [symmPart, scalarMatrix]
    · simp [symmPart, scalarMatrix, hij, Ne.symm hij]
  rw [hsymm]
  ring

/-- The canonical zero-force affine lift, packaged in the Chapter-3 carrier,
has energy controlled by the finite-`2` upper ellipticity quantity. -/
theorem exists_aCutoffAffineDirichletLift_energy_le_LambdaSq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) {t : ℝ} (ht : 0 < t) (p : Vec d) :
    let ell : H1Function (openCubeSet Q) :=
      H1Function.affineOnIsSobolevRegularDomain
        (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p
    ∃ v : DirichletForcedCubeSolution Q (aCutoffFamily M L omega) (fun _ => 0),
      v.boundaryData = ell ∧
        localizedCoeffEnergyValue (openCubeSet Q)
            ((aCutoffFamily M L omega).coeffOn Q) v.toH1 ≤
          LambdaSq Q t (.finite 2) (aCutoffFamily M L omega) * vecNormSq p := by
  dsimp only
  let A := aCutoffFamily M L omega
  let aQ := A.coeffOn Q
  let hsymQ : aQ.IsSymmetric :=
    (aCutoffTriadicData M L omega).onCube Q |>.isSymmetric
  let b : Ch02.CoeffOn (cubeDomain Q) :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseSymmetricCoeffOn
      (cubeDomain Q) aQ hsymQ
  have hba : Ch02.CoeffOn.AEEq b aQ := by
    simpa only [b] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseSymmetricCoeffOn_ae_eq
        (cubeDomain Q) aQ hsymQ
  let ell : H1Function (openCubeSet Q) :=
    H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet Q) b.toCoeffField := by
    simpa only [b, Ch02.cubeDomain_coe] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseSymmetricCoeffOn_isEllipticFieldOn
        (cubeDomain Q) aQ hsymQ
  let X := oneStepDirichletCellMinimizer Q hEll (fun _ => p)
    (MeasureTheory.memLp_const p)
  let v : DirichletForcedCubeSolution Q A (fun _ => 0) :=
    { toH1 := X.affineFunction
      boundaryData := ell
      weakSolution := by
        intro phi
        have hweak := X.weakDivergenceFree hEll (MeasureTheory.memLp_const p) phi
        calc
          ∫ x in openCubeSet Q,
              vecDot (matVecMul ((A.coeffOn Q).toCoeffField x)
                (X.affineFunction.grad x)) (phi.toH1Function.grad x) ∂volume =
              ∫ x in openCubeSet Q,
                vecDot (matVecMul (b.toCoeffField x)
                  (X.affineFunction.grad x)) (phi.toH1Function.grad x) ∂volume := by
                apply integral_congr_ae
                filter_upwards [hba] with x hx
                simp only [A, aQ] at hx
                rw [hx]
          _ = 0 := by
            simpa [X, OneStepDirichletCellMinimizer.affineFunction,
              OneStepDirichletCellMinimizer.field,
              H1Function.affineOnIsSobolevRegularDomain_grad] using hweak
          _ = ∫ x in openCubeSet Q,
              vecDot ((fun _ : Vec d => (0 : Vec d)) x)
                (phi.toH1Function.grad x) ∂volume := by simp [vecDot]
      zeroTraceDifference := by
        refine ⟨X.correction, ?_⟩
        filter_upwards with x
        simp [X, ell, OneStepDirichletCellMinimizer.affineFunction] }
  have hAffine : IsAffineDirichletSolution b.toCoeffField (openCubeSet Q) p
      X.affineFunction := X.isAffineDirichletSolution hEll
  have hSymB : IsSymmetricCoeffField b.toCoeffField := by
    simpa only [b] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseSymmetricCoeffOn_isSymmetricCoeffField
        (cubeDomain Q) aQ hsymQ
  have hSymBPublic : b.IsSymmetric := Filter.Eventually.of_forall hSymB
  have hMin : IsSymmetricDirichletMinimizer (cubeDomain Q) b p X.affineFunction :=
    Homogenization.Internal.Ch02.BookCh02.isSymmetricDirichletMinimizer_of_isAffineDirichletSolution
      (cubeDomain Q) b hAffine hSymB hEll
  have hTheory := responseSymmetricDirichletNeumannTheory (cubeDomain Q) b
    hSymBPublic
  have hEnergy : localizedCoeffEnergyValue (openCubeSet Q) aQ X.affineFunction =
      vecDot p (matVecMul (Ch02.sigmaCoarse (cubeDomain Q) aQ) p) := by
    have hNu :=
      Homogenization.Internal.Ch02.BookCh02.symmetricDirichletNu_eq_of_minimizer hMin
    have hValue := hTheory.dirichlet_value_by_sigma p
    rw [hNu] at hValue
    have hEnergyAE := Ch02.symmetricDirichletEnergyValue_eq_ofAEEq hba X.affineFunction
    have hSigmaAE := Ch02.sigmaCoarse_eq_ofAEEq hba
    rw [localized_energy_eq_two_mul_symmetricDirichletEnergy M L omega Q]
    rw [← hEnergyAE, ← hSigmaAE]
    nlinarith only [hValue]
  have hSigmaBHalf := (Ch02.sigmaCoarse_le_bCoarse (cubeDomain Q) aQ) p
  have hSigmaB : vecDot p (matVecMul (Ch02.sigmaCoarse (cubeDomain Q) aQ) p) ≤
      vecDot p (matVecMul (Ch02.bCoarse (cubeDomain Q) aQ) p) := by
    nlinarith only [hSigmaBHalf]
  have hBquad := vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
    (bCoarse_posSemidef (cubeDomain Q) aQ) p
  have hBnorm : matrixOperatorNorm (bCoarse (cubeDomain Q) aQ) ≤
      LambdaSq Q t (.finite 2) A := by
    rw [← matrixNorm_eq_matrixOperatorNorm]
    exact oneCube_b_le_LambdaSq_finite Q A ht (by norm_num)
  have hp0 : 0 ≤ vecNormSq p := vecNormSq_nonneg p
  have hbound : vecDot p (matVecMul (Ch02.sigmaCoarse (cubeDomain Q) aQ) p) ≤
      LambdaSq Q t (.finite 2) A * vecNormSq p := by
    calc
      _ ≤ vecDot p (matVecMul (bCoarse (cubeDomain Q) aQ) p) := hSigmaB
      _ ≤ matrixOperatorNorm (bCoarse (cubeDomain Q) aQ) * vecNormSq p := hBquad
      _ ≤ LambdaSq Q t (.finite 2) A * vecNormSq p :=
        mul_le_mul_of_nonneg_right hBnorm hp0
  refine ⟨v, rfl, ?_⟩
  rw [show localizedCoeffEnergyValue (openCubeSet Q)
      ((aCutoffFamily M L omega).coeffOn Q) v.toH1 =
      vecDot p (matVecMul (Ch02.sigmaCoarse (cubeDomain Q) aQ) p) by
        simpa only [v, A, aQ] using hEnergy]
  exact hbound

/-- Good-event normalized form of the affine-mode price. -/
theorem exists_aCutoffAffineDirichletLift_energy_le_normalizedCap
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) {t sigma K : ℝ}
    (ht : 0 < t) (hsigma : 0 < sigma)
    (hcap : sigma⁻¹ * LambdaSq Q t (.finite 2)
      (aCutoffFamily M L omega) ≤ K) (p : Vec d) :
    let ell : H1Function (openCubeSet Q) :=
      H1Function.affineOnIsSobolevRegularDomain
        (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p
    ∃ v : DirichletForcedCubeSolution Q (aCutoffFamily M L omega) (fun _ => 0),
      v.boundaryData = ell ∧
        localizedCoeffEnergyValue (openCubeSet Q)
            ((aCutoffFamily M L omega).coeffOn Q) v.toH1 ≤
          K * sigma * vecNormSq p := by
  dsimp only
  obtain ⟨v, hv, henergy⟩ :=
    exists_aCutoffAffineDirichletLift_energy_le_LambdaSq M L omega Q ht p
  refine ⟨v, hv, henergy.trans ?_⟩
  have hLambda : LambdaSq Q t (.finite 2) (aCutoffFamily M L omega) ≤ K * sigma := by
    have h := mul_le_mul_of_nonneg_left hcap hsigma.le
    rw [← mul_assoc, mul_inv_cancel₀ hsigma.ne', one_mul] at h
    simpa [mul_comm] using h
  exact mul_le_mul_of_nonneg_right hLambda (vecNormSq_nonneg p)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
