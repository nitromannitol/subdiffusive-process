module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.NormalizedCutoffLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.AhomStarCharacterization

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open Filter MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}



theorem annealedBlockMatrixAtScale_upperLeft_eq_abar [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) :
    (Ch04.annealedBlockMatrixAtScale (aCutoffRestrictionLaw M L)
      (n : ℤ)).upperLeft =
      abar M L (Ch02.cubeDomain (originCube d (n : ℤ))) := by
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

/-- **P-b.  The Section 5.7 annealed scalar limit of the normalized cutoff law
is the frozen homogenized coefficient `ahom M L`.** -/
theorem barSigmaLimit_normalizedCutoffLaw_eq_ahom [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Ch05.Section57.barSigmaLimit (normalizedCutoffLaw_lawCarrier M L)
        (normalizedCutoffLaw_structuralLaw M L) = ahom M L := by
  let P := aCutoffRestrictionLaw M L
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  let k := aCutoffNormalizationDepth d L
  let hStruct := aCutoffNormalization_structuralLaw M L
  let hP4 := aCutoffNormalization_quantitativeCoarseGrainedEllipticity M L
  let ell := Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct
  have hfull := annealedFullBlockMatrixAtScale_tendsto_of_scaleNormalized_P4
    hP k hStruct hP4
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
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
    exact congrFun (congrFun
      (annealedBlockMatrixAtScale_upperLeft_eq_abar M L n) i) i
  have hahom0 := tendsto_pi_nhds.mp (tendsto_abar_originCube_ahom M L) i
  have hahom := tendsto_pi_nhds.mp hahom0 i
  have hahom' : Tendsto (fun n : ℕ =>
      abar M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i)
      atTop (nhds (ahom M L)) := by
    simpa [Matrix.one_apply] using hahom
  have : ell = ahom M L := tendsto_nhds_unique hcoarse hahom'
  simpa [normalizedCutoffLaw_lawCarrier, normalizedCutoffLaw_structuralLaw,
    hP, k, hStruct, ell] using! this

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
