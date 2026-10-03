module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.NormalizerIdentification
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualPrefixSuffix

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}



theorem annealedBlockMatrixAtScale_lowerRight_eq_abarStarInv [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) :
    (Ch04.annealedBlockMatrixAtScale (aCutoffRestrictionLaw M L)
      (n : ℤ)).lowerRight =
      abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) := by
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  ext i j
  rw [abarStarInv, Ch04.annealedBlockMatrixAtScale, Ch04.annealedBlockMatrix,
    aCutoffRestrictionLaw_eq_map]
  change (∫ a : RegCoeffField d,
      (coarseBlockMatrix (cubeSet (originCube d (n : ℤ))) a.toFun).lowerRight i j
        ∂Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure) =
    (∫ omega, (randomAStarMatrix M L
      (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ ∂M.P.toMeasure) i j
  rw [integral_matrix_apply (integrable_randomAStarMatrix_inv M L
    (Ch02.cubeDomain (originCube d (n : ℤ)))) i j]
  rw [integral_map (measurable_aCutoffRegCoeffField M L).aemeasurable
    ((hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
      (originCube d (n : ℤ)) i j).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with omega
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  change (coarseBlockMatrix (openCubeSet (originCube d (n : ℤ)))
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))).lowerRight i j =
    (randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j
  have hmat : (coarseBlockMatrix (openCubeSet (originCube d (n : ℤ)))
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))).lowerRight =
      (randomAStarMatrix M L
        (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ := by
    let U := Ch02.cubeDomain (originCube d (n : ℤ))
    let hdata := aCutoffCoeffOnData M L omega U
    let aQ := hdata.toCoeffOn
    have hcoarse := isCoarseBlockMatrix_ch02_aCutoff M L omega
      (originCube d (n : ℤ))
    have hEq : Ch02.coarseBlockMatrix U aQ =
        coarseBlockMatrix (openCubeSet (originCube d (n : ℤ)))
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) :=
      eq_coarseBlockMatrix_of_isCoarseBlockMatrix hcoarse
    have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U aQ
      hdata.isSymmetric
    have hstar : (Ch02.aStarCoarse U aQ)⁻¹ = Ch02.sigmaStarInvCoarse U aQ := by
      rw [hTheory.derived_matrices.2.1]
      unfold Ch02.sigmaStarCoarse
      exact Matrix.nonsing_inv_nonsing_inv _
        (Ch02.isUnit_det_sigmaStarInvCoarse U aQ)
    calc
      (coarseBlockMatrix (openCubeSet (originCube d (n : ℤ)))
            (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))).lowerRight
          = (Ch02.coarseBlockMatrix U aQ).lowerRight := by rw [hEq]
        _ = Ch02.sigmaStarInvCoarse U aQ := Ch02.coarseBlockMatrix_lowerRight U aQ
        _ = (Ch02.aStarCoarse U aQ)⁻¹ := hstar.symm
        _ = (randomAStarMatrix M L U omega)⁻¹ := rfl
  exact congrFun (congrFun hmat i) j

/-- Scalar extraction: two scalar matrices agree iff their scalars agree. -/
private theorem scalar_of_smul_one_eq [NeZero d] {a b : ℝ}
    (h : a • (1 : Mat d) = b • (1 : Mat d)) : a = b := by
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have := congrFun (congrFun h i) i
  simpa [Matrix.one_apply, Matrix.smul_apply] using this

/-- **3c, primal half.** -/
theorem barSigmaAtScale_normalizedCutoffLaw_eq_abarScalarReadout [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    (normalizedCutoffLaw_lawCarrier M L).barSigmaAtScale
        (normalizedCutoffLaw_structuralLaw M L) (m : ℤ) =
      abarScalarReadout M L (aCutoffNormalizationDepth d L + m) := by
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  let k := aCutoffNormalizationDepth d L
  refine scalar_of_smul_one_eq (d := d) ?_
  calc
    (normalizedCutoffLaw_lawCarrier M L).barSigmaAtScale
          (normalizedCutoffLaw_structuralLaw M L) (m : ℤ) • (1 : Mat d)
        = Ch04.annealedSigmaAtScale (normalizedCutoffLaw M L) (m : ℤ) :=
          ((normalizedCutoffLaw_lawCarrier M L).annealedSigmaAtScale_eq_barSigmaAtScale
            (normalizedCutoffLaw_structuralLaw M L) (m : ℤ)).symm
    _ = Ch04.annealedBAtScale (normalizedCutoffLaw M L) (m : ℤ) := by
          rw [(normalizedCutoffLaw_lawCarrier M L).annealedSigmaAtScale_eq_barSigmaAtScale
            (normalizedCutoffLaw_structuralLaw M L) (m : ℤ),
            (normalizedCutoffLaw_lawCarrier M L).annealedBAtScale_eq_barBAtScale
              (normalizedCutoffLaw_structuralLaw M L) (m : ℤ),
            (normalizedCutoffLaw_lawCarrier M L).barSigmaAtScale_eq_barBAtScale
              (normalizedCutoffLaw_structuralLaw M L) (m : ℤ)]
    _ = Ch04.annealedBAtScale (aCutoffRestrictionLaw M L) ((k + m : ℕ) : ℤ) :=
          Ch04.annealedBAtScale_restrictionScaleNormalizedLaw
            hP k m
    _ = (Ch04.annealedBlockMatrixAtScale (aCutoffRestrictionLaw M L)
          ((k + m : ℕ) : ℤ)).upperLeft := rfl
    _ = abar M L (Ch02.cubeDomain (originCube d ((k + m : ℕ) : ℤ))) :=
          annealedBlockMatrixAtScale_upperLeft_eq_abar M L (k + m)
    _ = abarScalarReadout M L (k + m) • (1 : Mat d) :=
          abar_eq_abarScalarReadout_smul_one M L (k + m)

/-- **3c, dual half.** -/
theorem barSigmaStarInvAtScale_normalizedCutoffLaw_eq_dualReadout [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    (normalizedCutoffLaw_lawCarrier M L).barSigmaStarInvAtScale
        (normalizedCutoffLaw_structuralLaw M L) (m : ℤ) =
      oneStepAnnealedDualReadout M L (aCutoffNormalizationDepth d L + m) := by
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  let k := aCutoffNormalizationDepth d L
  refine scalar_of_smul_one_eq (d := d) ?_
  calc
    (normalizedCutoffLaw_lawCarrier M L).barSigmaStarInvAtScale
          (normalizedCutoffLaw_structuralLaw M L) (m : ℤ) • (1 : Mat d)
        = Ch04.annealedSigmaStarInvAtScale (normalizedCutoffLaw M L) (m : ℤ) :=
          ((normalizedCutoffLaw_lawCarrier M L).annealedSigmaStarInvAtScale_eq_barSigmaStarInvAtScale
            (normalizedCutoffLaw_structuralLaw M L) (m : ℤ)).symm
    _ = Ch04.annealedSigmaStarInvAtScale (aCutoffRestrictionLaw M L)
          ((k + m : ℕ) : ℤ) :=
          Ch04.annealedSigmaStarInvAtScale_restrictionScaleNormalizedLaw
            hP k m
    _ = (Ch04.annealedBlockMatrixAtScale (aCutoffRestrictionLaw M L)
          ((k + m : ℕ) : ℤ)).lowerRight := rfl
    _ = abarStarInv M L (Ch02.cubeDomain (originCube d ((k + m : ℕ) : ℤ))) :=
          annealedBlockMatrixAtScale_lowerRight_eq_abarStarInv M L (k + m)
    _ = oneStepAnnealedDualReadout M L (k + m) • (1 : Mat d) :=
          abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one M L (k + m)



theorem thetaAtScale_normalizedCutoffLaw_eq_campaignContrast [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    Ch05.thetaAtScale (normalizedCutoffLaw_lawCarrier M L)
        (normalizedCutoffLaw_structuralLaw M L) (m : ℤ) =
      abarScalarReadout M L (aCutoffNormalizationDepth d L + m) *
        oneStepAnnealedDualReadout M L (aCutoffNormalizationDepth d L + m) := by
  rw [Ch05.thetaAtScale_eq, Ch04.RestrictionLawCarrier.thetaAtScale,
    (normalizedCutoffLaw_lawCarrier M L).barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale
      (normalizedCutoffLaw_structuralLaw M L) (m : ℤ),
    inv_inv,
    barSigmaAtScale_normalizedCutoffLaw_eq_abarScalarReadout M L m,
    barSigmaStarInvAtScale_normalizedCutoffLaw_eq_dualReadout M L m]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
