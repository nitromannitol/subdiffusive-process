module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4
public import SubdiffusiveProcess.CoarseGrainingVocab.AhomCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedLimitP4
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseMeasureTheory

@[expose] public section

/-!
# Starred characterization of the GMC homogenized coefficient

The normalized cutoff law satisfies the structural and `(P4)` hypotheses.
The P4 annealed full-block limit is transported back to the literal
`abar`/`abarStarInv` wrappers; uniqueness against the already-landed primal
`ahom` limit identifies the common scalar.

PROVENANCE: mirrors
`Algsuperdiff/Section3/Annealed/RunningDiffusivityBridge.lean` and the
lower-right-entry extraction in
`Algsuperdiff/Section3/Provider/Homogenization/SigmaBarAnchor.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization Homogenization.Book
open scoped Matrix.Norms.Elementwise

noncomputable section



private theorem coarseBlockMatrix_lowerRight_eq_randomAStarInv
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    (coarseBlockMatrix (openCubeSet Q)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))).lowerRight =
      (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ := by
  let U := Ch02.cubeDomain Q
  let hdata := aCutoffCoeffOnData M L omega U
  let aQ := hdata.toCoeffOn
  have hcoarse := isCoarseBlockMatrix_ch02_aCutoff M L omega Q
  have hEq : Ch02.coarseBlockMatrix U aQ =
      coarseBlockMatrix (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) :=
    eq_coarseBlockMatrix_of_isCoarseBlockMatrix hcoarse
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U aQ hdata.isSymmetric
  calc
    (coarseBlockMatrix (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))).lowerRight =
        (Ch02.coarseBlockMatrix U aQ).lowerRight := by rw [hEq]
    _ = Ch02.sigmaStarInvCoarse U aQ := Ch02.coarseBlockMatrix_lowerRight U aQ
    _ = (Ch02.aStarCoarse U aQ)⁻¹ := by
      have hstar : (Ch02.aStarCoarse U aQ)⁻¹ =
          Ch02.sigmaStarInvCoarse U aQ := by
        rw [hTheory.derived_matrices.2.1]
        unfold Ch02.sigmaStarCoarse
        exact Matrix.nonsing_inv_nonsing_inv _
          (Ch02.isUnit_det_sigmaStarInvCoarse U aQ)
      exact hstar.symm
    _ = (randomAStarMatrix M L U omega)⁻¹ := rfl

private theorem annealedBlockMatrix_upperLeft_eq_abar
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) :
    (Ch04.annealedBlockMatrixAtScale (aCutoffRestrictionLaw M L)
      (n : ℤ)).upperLeft =
      abar M L (Ch02.cubeDomain (originCube d (n : ℤ))) := by
  let P := aCutoffRestrictionLaw M L
  let f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → RegCoeffField d := aCutoffRegCoeffField M L
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  ext i j
  rw [abar, Ch04.annealedBlockMatrixAtScale, Ch04.annealedBlockMatrix,
    aCutoffRestrictionLaw_eq_map]
  change (∫ a : RegCoeffField d,
      (coarseBlockMatrix (cubeSet (originCube d (n : ℤ))) a.toFun).upperLeft i j
        ∂Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure) =
    (∫ omega, randomAMatrix M L
      (Ch02.cubeDomain (originCube d (n : ℤ))) omega ∂M.P.toMeasure) i j
  rw [integral_matrix_apply (integrable_randomAMatrix M L
    (Ch02.cubeDomain (originCube d (n : ℤ)))) i j]
  rw [integral_map (measurable_aCutoffRegCoeffField M L).aemeasurable
    ((hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
      (originCube d (n : ℤ)) i j).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with omega
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  change (coarseBlockMatrix (openCubeSet (originCube d (n : ℤ)))
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))).upperLeft i j =
    randomAMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) omega i j
  rw [coarseBlockMatrix_upperLeft_eq_sigmaCoarse_aCutoff M L omega
    (originCube d (n : ℤ))]
  rw [randomAMatrix_eq_rawSigmaCoarse]

private theorem annealedBlockMatrix_lowerRight_eq_abarStarInv
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) :
    (Ch04.annealedBlockMatrixAtScale (aCutoffRestrictionLaw M L)
      (n : ℤ)).lowerRight =
      abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) := by
  let P := aCutoffRestrictionLaw M L
  let f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → RegCoeffField d := aCutoffRegCoeffField M L
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
  exact congrFun (congrFun
    (coarseBlockMatrix_lowerRight_eq_randomAStarInv M L omega
      (originCube d (n : ℤ))) i) j

private theorem commonLimit_eq_ahom {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    letI : NeZero d := ⟨Nat.ne_of_gt
      (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
    Ch05.Section57.barSigmaLimit
      ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
        (aCutoffNormalizationDepth d L))
      (aCutoffNormalization_structuralLaw M L) = ahom M L := by
  letI : NeZero d := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let P := aCutoffRestrictionLaw M L
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  let k := aCutoffNormalizationDepth d L
  let hStruct := aCutoffNormalization_structuralLaw M L
  let hP4 := aCutoffNormalization_quantitativeCoarseGrainedEllipticity M L
  let ell := Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct
  have hfull := annealedFullBlockMatrixAtScale_tendsto_of_scaleNormalized_P4
    hP k hStruct hP4
  let i : Fin d := ⟨0, lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension⟩
  have hentry0 := (tendsto_pi_nhds.mp hfull) (Sum.inl i)
  have hentry := (tendsto_pi_nhds.mp hentry0) (Sum.inl i)
  have hentry' : Tendsto (fun n : ℕ =>
      (Ch04.annealedBlockMatrixAtScale P (n : ℤ)).upperLeft i i)
      atTop (nhds ell) := by
    simpa [P, toFullBlockMat, Ch02.blockDiag, ell, Matrix.one_apply] using hentry
  have hcoarse : Tendsto (fun n : ℕ =>
      abar M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i)
      atTop (nhds ell) := by
    apply hentry'.congr'
    filter_upwards with n
    exact congrFun (congrFun (annealedBlockMatrix_upperLeft_eq_abar M L n) i) i
  have hahom0 := tendsto_pi_nhds.mp (tendsto_abar_originCube_ahom M L) i
  have hahom := tendsto_pi_nhds.mp hahom0 i
  have hahom' : Tendsto (fun n : ℕ =>
      abar M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i)
      atTop (nhds (ahom M L)) := by
    simpa [Matrix.one_apply] using hahom
  exact tendsto_nhds_unique hcoarse hahom'

/-- The centered-cube annealed inverse-star matrices converge to the inverse
of the literal primal homogenized coefficient. -/
theorem tendsto_abarStarInv_originCube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Tendsto
      (fun k : ℕ => abarStarInv M L
        (Ch02.cubeDomain (originCube d (k : ℤ))))
      atTop (nhds ((ahom M L)⁻¹ • (1 : Mat d))) := by
  letI : NeZero d := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let P := aCutoffRestrictionLaw M L
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  let k := aCutoffNormalizationDepth d L
  let hStruct := aCutoffNormalization_structuralLaw M L
  let hP4 := aCutoffNormalization_quantitativeCoarseGrainedEllipticity M L
  let ell := Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct
  have hell : ell = ahom M L := by
    simpa [P, hP, k, hStruct, ell] using commonLimit_eq_ahom M L
  have hfull := annealedFullBlockMatrixAtScale_tendsto_of_scaleNormalized_P4
    hP k hStruct hP4
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h0 := (tendsto_pi_nhds.mp hfull) (Sum.inr i)
  have h := (tendsto_pi_nhds.mp h0) (Sum.inr j)
  have h' : Tendsto (fun n : ℕ =>
      (Ch04.annealedBlockMatrixAtScale P (n : ℤ)).lowerRight i j)
      atTop (nhds ((ell⁻¹ • (1 : Mat d)) i j)) := by
    simpa [P, toFullBlockMat, Ch02.blockDiag, ell, Pi.smul_apply] using h
  have h'' : Tendsto (fun n : ℕ =>
      abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j)
      atTop (nhds ((ell⁻¹ • (1 : Mat d)) i j)) := by
    apply h'.congr'
    filter_upwards with n
    exact congrFun (congrFun (annealedBlockMatrix_lowerRight_eq_abarStarInv M L n) i) j
  simpa [hell] using h''

end

end SubdiffusiveProcess.CoarseGrainingVocab
