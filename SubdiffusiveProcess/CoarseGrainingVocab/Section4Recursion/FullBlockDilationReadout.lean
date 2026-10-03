module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ExpectationVarianceAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseRosenthal
public import Homogenization.Book.Ch04.Theorems.DilationResponse

@[expose] public section

/-!
# Full-block dilation readout for the Section 4 recursion

This file supplies the deterministic carrier identifications needed to apply
the Chapter 5 two-plus-eight variance estimate to the literal GMC cutoff
sample at every integer scale.

PROVENANCE: the arbitrary-integer dilation argument follows
`Algsuperdiff/Section3/Provider/Homogenization/RelativeLimitLoadBridge.lean`
and `CombineFiniteCarrierTransport.lean`.  The direct diagonal-normalizer
readout is the scalar specialization of the starred-block gauge in
`Algsuperdiff/Section3/Provider/Homogenization/VarianceClosure.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators Matrix.Norms.Elementwise MatrixOrder

noncomputable section


private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem dilatedCoeffFamily_coeffOn_ae_eq_dilateReg
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) (Q : TriadicCube d) :
    ((Ch02.TriadicCoeffFamily.dilate k
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)).coeffOn Q).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet Q)] (dilateReg k a).toFun := by
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Qsrc : TriadicCube d := Ch02.dilateCube (-k) Q
  have htarget : Ch02.dilateCube k Qsrc = Q := by
    simpa [Qsrc] using! Ch02.dilateCube_dilateCube_neg k Q
  have hD := Ch02.TriadicCoeffFamily.isDilation_dilate k F Qsrc
  have hcoeff' :
      ((Ch02.TriadicCoeffFamily.dilate k F).coeffOn
          (Ch02.dilateCube k Qsrc)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
          Ch02.dilateCoeffField k a.toFun := by
    simpa [F, Qsrc, htarget] using! hD.coeff_ae_eq
  have hcast := hcoeff'
  rw [htarget] at hcast
  simpa [F, Ch04.dilateReg_toFun] using! hcast

private theorem aelocallyUniformlyEllipticField_dilateReg
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) : Ch04.AELocallyUniformlyEllipticField (dilateReg k a) := by
  intro Q
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate k F
  let bQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := B.coeffOn Q
  have hcoeff : bQ.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (dilateReg k a).toFun := by
    simpa [bQ, B] using! dilatedCoeffFamily_coeffOn_ae_eq_dilateReg ha k Q
  refine ⟨bQ.lam, bQ.Lam, bQ.lam_pos, bQ.lam_le_Lam, ?_⟩
  refine ⟨measurableSet_openCubeSet Q, ?_, ?_⟩
  · intro i j
    refine (bQ.aeStronglyMeasurable i j).congr ?_
    filter_upwards [hcoeff] with x hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [restrictCoeffField, hxQ, hx]
    · simp [restrictCoeffField, hxQ]
  · filter_upwards [bQ.aeElliptic, hcoeff] with x hxEll hx
    simpa [hx] using! hxEll

private theorem triadicCoeffFamily_dilateReg_aeeq_dilate
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) :
    Ch02.TriadicCoeffFamily.AEEq
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (dilateReg k a) (aelocallyUniformlyEllipticField_dilateReg ha k))
      (Ch02.TriadicCoeffFamily.dilate k
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)) := by
  intro Q
  change (dilateReg k a).toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
    ((Ch02.TriadicCoeffFamily.dilate k
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)).coeffOn Q).toCoeffField
  simpa [Ch02.cubeDomain_coe] using!
    (dilatedCoeffFamily_coeffOn_ae_eq_dilateReg ha k Q).symm

/-- The deterministic coarse block matrix shifts on an arbitrary triadic cube
under an arbitrary integer dilation of the coefficient field. -/
theorem coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) (Q : TriadicCube d) :
    coarseBlockMatrix (cubeSet Q) (dilateReg k a).toFun =
      coarseBlockMatrix (cubeSet (Ch02.dilateCube (-k) Q)) a.toFun := by
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let hk := aelocallyUniformlyEllipticField_dilateReg ha k
  let G : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (dilateReg k a) hk
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate k F
  let Qsrc : TriadicCube d := Ch02.dilateCube (-k) Q
  have htarget : Ch02.dilateCube k Qsrc = Q := by
    simpa [Qsrc] using! Ch02.dilateCube_dilateCube_neg k Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F, hk] using!
      triadicCoeffFamily_dilateReg_aeeq_dilate ha k
  have hAEEq := Ch02.coarseBlockMatrix_eq_ofAEEq (hGB Q)
  have hdilate := Ch02.coarseBlockMatrix_dilate
    (Ch02.TriadicCoeffFamily.isDilation_dilate k F Qsrc)
  have hdilate' :
      Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (B.coeffOn Q) =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) := by
    rw [htarget] at hdilate
    simpa [B] using! hdilate
  calc
    coarseBlockMatrix (cubeSet Q) (dilateReg k a).toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (G.coeffOn Q) := by
      simpa [G] using!
        Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
          hk Q
    _ = Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (B.coeffOn Q) := hAEEq
    _ = Ch02.coarseBlockMatrix (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) := hdilate'
    _ = coarseBlockMatrix (cubeSet Qsrc) a.toFun :=
      (Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Qsrc).symm

/-- Annealed coarse block matrices shift under an arbitrary integer dilation
pushforward. -/
theorem annealedBlockMatrix_map_dilateReg_cube
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (k : ℤ)
    (hPk : Ch04.RestrictionLawCarrier (Measure.map (dilateReg k) P))
    (Q : TriadicCube d) :
    Ch04.annealedBlockMatrix (Measure.map (dilateReg k) P) (cubeSet Q) =
      Ch04.annealedBlockMatrix P
        (cubeSet (Ch02.dilateCube (-k) Q)) := by
  unfold Ch04.annealedBlockMatrix
  refine blockMat_ext ?_ ?_ ?_ ?_
  · ext i j
    dsimp only
    rw [integral_map (measurable_dilateReg (d := d) k).aemeasurable]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      exact congrArg (fun A : BlockMat d => A.upperLeft i j)
        (coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic ha k Q)
    · exact (hPk.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
        Q i j).aestronglyMeasurable
  · ext i j
    dsimp only
    rw [integral_map (measurable_dilateReg (d := d) k).aemeasurable]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      exact congrArg (fun A : BlockMat d => A.upperRight i j)
        (coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic ha k Q)
    · exact (hPk.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet
        Q i j).aestronglyMeasurable
  · ext i j
    dsimp only
    rw [integral_map (measurable_dilateReg (d := d) k).aemeasurable]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      exact congrArg (fun A : BlockMat d => A.lowerLeft i j)
        (coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic ha k Q)
    · exact (hPk.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
        Q i j).aestronglyMeasurable
  · ext i j
    dsimp only
    rw [integral_map (measurable_dilateReg (d := d) k).aemeasurable]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      exact congrArg (fun A : BlockMat d => A.lowerRight i j)
        (coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic ha k Q)
    · exact (hPk.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
        Q i j).aestronglyMeasurable

private theorem dilateCube_originCube_sub (d : ℕ) (m s : ℤ) :
    Ch02.dilateCube s (originCube d (m - s)) = originCube d m := by
  simp [Ch02.dilateCube, originCube]

/-- The normalized law's annealed block at the possibly negative scale
`n-k` is the original law's annealed block at scale `n`. -/
theorem annealedBlockMatrixAtScale_scaleNormalized_sub
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (k : ℕ)
    (hPk : Ch04.RestrictionLawCarrier
      (Ch04.restrictionScaleNormalizedLaw k P)) (n : ℤ) :
    Ch04.annealedBlockMatrixAtScale
        (Ch04.restrictionScaleNormalizedLaw k P) (n - k) =
      Ch04.annealedBlockMatrixAtScale P n := by
  rw [Ch04.restrictionScaleNormalizedLaw]
  have h := annealedBlockMatrix_map_dilateReg_cube hP (-(k : ℤ)) hPk
    (originCube d (n - k))
  rw [show -(-(k : ℤ)) = (k : ℤ) by omega,
    dilateCube_originCube_sub d n k] at h
  simpa [Ch04.annealedBlockMatrixAtScale] using! h

/-- Literal finite-cutoff lower-right block readout on an arbitrary triadic
cube. -/
theorem coarseBlockMatrix_aCutoff_lowerRight_eq_randomAStarInv
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) :
    (coarseBlockMatrix (cubeSet Q) (aCutoffRegCoeffField M L omega).toFun).lowerRight =
      (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ := by
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]
  let U := Ch02.cubeDomain Q
  let hdata := aCutoffCoeffOnData M L omega U
  have hcoarse := isCoarseBlockMatrix_ch02_aCutoff M L omega Q
  have hEq : Ch02.coarseBlockMatrix U hdata.toCoeffOn =
      coarseBlockMatrix (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) :=
    eq_coarseBlockMatrix_of_isCoarseBlockMatrix hcoarse
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  change (coarseBlockMatrix (openCubeSet Q)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))).lowerRight =
    (randomAStarMatrix M L U omega)⁻¹
  rw [← hEq, Ch02.coarseBlockMatrix_lowerRight]
  rw [show randomAStarMatrix M L U omega = Ch02.aStarCoarse U hdata.toCoeffOn by rfl,
    hTheory.derived_matrices.2.1]
  exact (Matrix.nonsing_inv_nonsing_inv _
    (Ch02.isUnit_det_sigmaStarInvCoarse U hdata.toCoeffOn)).symm

/-- The lower-right block of the cutoff law's annealed matrix is the literal
`abarStarInv`. -/
theorem annealedBlockMatrix_aCutoff_lowerRight_eq_abarStarInv
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (Q : TriadicCube d) :
    (Ch04.annealedBlockMatrix (aCutoffRestrictionLaw M L) (cubeSet Q)).lowerRight =
      abarStarInv M L (Ch02.cubeDomain Q) := by
  ext i j
  rw [Ch04.annealedBlockMatrix, abarStarInv, aCutoffRestrictionLaw_eq_map]
  simp only
  change (∫ a : RegCoeffField d,
      (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j
        ∂Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure) =
    (∫ omega,
      (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹
        ∂M.P.toMeasure) i j
  rw [integral_matrix_apply
    (integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain Q)) i j]
  rw [integral_map (measurable_aCutoffRegCoeffField M L).aemeasurable
    (((aCutoffRestrictionLaw_lawCarrier M L)
      |>.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j)
        |>.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with omega
  exact congrFun (congrFun
    (coarseBlockMatrix_aCutoff_lowerRight_eq_randomAStarInv M L omega Q) i) j

/-- The possibly-negative normalized center carries the literal physical
finite-volume annealed inverse-star matrix. -/
theorem scalarAnnealedBlockMatrixAtScale_normalized_sub_lowerRight_eq_abarStarInv
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (n : ℤ) :
    (Ch04.scalarAnnealedBlockMatrixAtScale
      ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
        (aCutoffNormalizationDepth d L))
      (aCutoffNormalization_structuralLaw M L)
      (n - (aCutoffNormalizationDepth d L : ℤ))).lowerRight =
        abarStarInv M L (Ch02.cubeDomain (originCube d n)) := by
  let k := aCutoffNormalizationDepth d L
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  let hPk := hP.scaleNormalized k
  let hStruct := aCutoffNormalization_structuralLaw M L
  rw [← Ch05.Section54.VarianceBoundGoodScale.annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
    hPk hStruct]
  rw [annealedBlockMatrixAtScale_scaleNormalized_sub hP k hPk n]
  exact annealedBlockMatrix_aCutoff_lowerRight_eq_abarStarInv M L (originCube d n)

/-- Pointwise arbitrary-integer dilation of the random inverse-star block. -/
theorem normalizedCoarseBlock_lowerRight_eq_randomAStarInv
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (n : ℤ) :
    (coarseBlockMatrix
      (cubeSet (originCube d (n - (aCutoffNormalizationDepth d L : ℤ))))
      (rescaleReg (aCutoffNormalizationDepth d L)
        (aCutoffRegCoeffField M L omega)).toFun).lowerRight =
      (randomAStarMatrix M L
        (Ch02.cubeDomain (originCube d n)) omega)⁻¹ := by
  let k := aCutoffNormalizationDepth d L
  rw [Ch04.rescaleReg_eq_dilateReg_neg_nat]
  rw [coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic
    (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)]
  rw [show -(-(k : ℤ)) = (k : ℤ) by omega,
    dilateCube_originCube_sub d n k]
  exact coarseBlockMatrix_aCutoff_lowerRight_eq_randomAStarInv
    M L omega (originCube d n)

/-! ## Diagonal full-block normalizers and literal lower-right readout -/

/-- The lower-right part of the manuscript's `B⁻¹²` normalizer.  The
Chapter 5 endpoint allows an arbitrary normalizer, so the unused primal block
is set to zero rather than introducing a second moment channel. -/
def combineInvSqrtNormalizer {d : ℕ} (alpha : ℝ) : FullBlockMat d :=
  Matrix.diagonal fun
    | Sum.inl _ => 0
    | Sum.inr _ => Real.sqrt alpha

/-- The inverse diagonal normalizer used in the trace-response term. -/
def combineSqrtNormalizer {d : ℕ} (alpha : ℝ) : FullBlockMat d :=
  Matrix.diagonal fun
    | Sum.inl _ => 0
    | Sum.inr _ => (Real.sqrt alpha)⁻¹

private theorem diagonal_mul_mul_diagonal_apply {d : ℕ}
    (r : BlockCoord d → ℝ) (X : FullBlockMat d) (alpha beta : BlockCoord d) :
    (Matrix.diagonal r * X * Matrix.diagonal r) alpha beta =
      r alpha * X alpha beta * r beta := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq,
    Finset.sum_ite_eq', mul_comm, mul_left_comm]

private theorem combineInvSqrtNormalizer_inr {d : ℕ} (alpha : ℝ)
    (i : Fin d) :
  combineInvSqrtNormalizer alpha (Sum.inr i) (Sum.inr i) = Real.sqrt alpha := by
  simp [combineInvSqrtNormalizer]

private theorem transpose_combineInvSqrtNormalizer {d : ℕ} (alpha : ℝ) :
    Matrix.transpose (combineInvSqrtNormalizer (d := d) alpha) =
      combineInvSqrtNormalizer alpha := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [combineInvSqrtNormalizer]
  · simp [combineInvSqrtNormalizer, h, Ne.symm h]

/-- **Identification 1.**  On the arbitrary integer normalized cube, the
lower-right entry of the Chapter 5 full-block fluctuation is exactly `ahom`
times the centered literal inverse-star entry on the physical cube. -/
theorem fullBlockFluctuation_lowerRight_eq_centered_randomAStarInv
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (n : ℤ) (i j : Fin d) :
    Ch05.Section56.fullBlockFluctuationMatrixWithNormalizer
      ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
        (aCutoffNormalizationDepth d L))
      (aCutoffNormalization_structuralLaw M L)
      (n - (aCutoffNormalizationDepth d L : ℤ))
      (combineInvSqrtNormalizer (ahom M L))
      (cubeSet (originCube d
        (n - (aCutoffNormalizationDepth d L : ℤ))))
      (rescaleReg (aCutoffNormalizationDepth d L)
        (aCutoffRegCoeffField M L omega))
      (Sum.inr i) (Sum.inr j) =
        ahom M L *
          ((randomAStarMatrix M L
              (Ch02.cubeDomain (originCube d n)) omega)⁻¹ i j -
            abarStarInv M L (Ch02.cubeDomain (originCube d n)) i j) := by
  let alpha := ahom M L
  have halpha : 0 < alpha := by simpa [alpha] using! ahom_pos M L
  let hP := (aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
    (aCutoffNormalizationDepth d L)
  let hStruct := aCutoffNormalization_structuralLaw M L
  let center : ℤ := n - (aCutoffNormalizationDepth d L : ℤ)
  let Q : TriadicCube d := originCube d center
  let a := rescaleReg (aCutoffNormalizationDepth d L)
    (aCutoffRegCoeffField M L omega)
  let X : FullBlockMat d :=
    toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) -
      toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
  change ((Matrix.transpose (combineInvSqrtNormalizer alpha) * X *
      combineInvSqrtNormalizer alpha : FullBlockMat d)
        (Sum.inr i) (Sum.inr j)) = _
  rw [transpose_combineInvSqrtNormalizer]
  unfold combineInvSqrtNormalizer
  rw [diagonal_mul_mul_diagonal_apply]
  simp only
  have hsqrt : Real.sqrt alpha * Real.sqrt alpha = alpha :=
    Real.mul_self_sqrt halpha.le
  have hrandom := normalizedCoarseBlock_lowerRight_eq_randomAStarInv
    M L omega n
  have hcenter :=
    scalarAnnealedBlockMatrixAtScale_normalized_sub_lowerRight_eq_abarStarInv
      M L n
  change Real.sqrt alpha *
      ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j -
        (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center).lowerRight i j) *
      Real.sqrt alpha = _
  rw [show (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight =
      (randomAStarMatrix M L (Ch02.cubeDomain (originCube d n)) omega)⁻¹ by
        simpa [Q, a, center] using! hrandom,
    show (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center).lowerRight =
      abarStarInv M L (Ch02.cubeDomain (originCube d n)) by
        simpa [hP, hStruct, center] using! hcenter]
  let x : ℝ :=
    (randomAStarMatrix M L (Ch02.cubeDomain (originCube d n)) omega)⁻¹ i j -
      abarStarInv M L (Ch02.cubeDomain (originCube d n)) i j
  change Real.sqrt alpha * x * Real.sqrt alpha = alpha * x
  calc
    Real.sqrt alpha * x * Real.sqrt alpha =
        (Real.sqrt alpha * Real.sqrt alpha) * x := by ring
    _ = alpha * x := by rw [hsqrt]

/-- Arbitrary normalized-cube version of the lower-right readout; its physical
cube is obtained by dilating from normalized coordinates. -/
theorem fullBlockFluctuation_lowerRight_eq_centered_randomAStarInv_dilateCube
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (n : ℤ) (R : TriadicCube d) (i j : Fin d) :
    Ch05.Section56.fullBlockFluctuationMatrixWithNormalizer
      ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
        (aCutoffNormalizationDepth d L))
      (aCutoffNormalization_structuralLaw M L)
      (n - (aCutoffNormalizationDepth d L : ℤ))
      (combineInvSqrtNormalizer (ahom M L)) (cubeSet R)
      (rescaleReg (aCutoffNormalizationDepth d L)
        (aCutoffRegCoeffField M L omega))
      (Sum.inr i) (Sum.inr j) =
        ahom M L *
          ((randomAStarMatrix M L
              (Ch02.cubeDomain (Ch02.dilateCube
                (aCutoffNormalizationDepth d L : ℤ) R)) omega)⁻¹ i j -
            abarStarInv M L (Ch02.cubeDomain (originCube d n)) i j) := by
  let alpha := ahom M L
  let k := aCutoffNormalizationDepth d L
  let hP := (aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized k
  let hStruct := aCutoffNormalization_structuralLaw M L
  let center : ℤ := n - (k : ℤ)
  let a := rescaleReg k (aCutoffRegCoeffField M L omega)
  let X : FullBlockMat d :=
    toFullBlockMat (coarseBlockMatrix (cubeSet R) a.toFun) -
      toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
  have halpha : 0 < alpha := by simpa [alpha] using! ahom_pos M L
  have hsqrt : Real.sqrt alpha * Real.sqrt alpha = alpha :=
    Real.mul_self_sqrt halpha.le
  change ((Matrix.transpose (combineInvSqrtNormalizer alpha) * X *
      combineInvSqrtNormalizer alpha : FullBlockMat d)
        (Sum.inr i) (Sum.inr j)) = _
  rw [transpose_combineInvSqrtNormalizer]
  unfold combineInvSqrtNormalizer
  rw [diagonal_mul_mul_diagonal_apply]
  change Real.sqrt alpha *
      ((coarseBlockMatrix (cubeSet R) a.toFun).lowerRight i j -
        (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center).lowerRight i j) *
      Real.sqrt alpha = _
  have hcoarse := coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic
    (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
    (-(k : ℤ)) R
  rw [show -(-(k : ℤ)) = (k : ℤ) by omega] at hcoarse
  have hrandom : (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight =
      (randomAStarMatrix M L
        (Ch02.cubeDomain (Ch02.dilateCube (k : ℤ) R)) omega)⁻¹ := by
    rw [show coarseBlockMatrix (cubeSet R) a.toFun =
        coarseBlockMatrix (cubeSet (Ch02.dilateCube (k : ℤ) R))
          (aCutoffRegCoeffField M L omega).toFun by
      simpa [a, Ch04.rescaleReg_eq_dilateReg_neg_nat] using! hcoarse]
    exact coarseBlockMatrix_aCutoff_lowerRight_eq_randomAStarInv
      M L omega (Ch02.dilateCube (k : ℤ) R)
  have hcenter :=
    scalarAnnealedBlockMatrixAtScale_normalized_sub_lowerRight_eq_abarStarInv
      M L n
  rw [hrandom,
    show (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center).lowerRight =
      abarStarInv M L (Ch02.cubeDomain (originCube d n)) by
        simpa [hP, hStruct, center, k] using! hcenter]
  let x : ℝ :=
    (randomAStarMatrix M L
      (Ch02.cubeDomain (Ch02.dilateCube (k : ℤ) R)) omega)⁻¹ i j -
      abarStarInv M L (Ch02.cubeDomain (originCube d n)) i j
  change Real.sqrt alpha * x * Real.sqrt alpha = alpha * x
  calc
    Real.sqrt alpha * x * Real.sqrt alpha =
        (Real.sqrt alpha * Real.sqrt alpha) * x := by ring
    _ = alpha * x := by rw [hsqrt]

private theorem adjointReg_rescale_aCutoff_eq
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k : ℕ)
    (omega : Sample d) :
    adjointReg (rescaleReg k (aCutoffRegCoeffField M L omega)) =
      rescaleReg k (aCutoffRegCoeffField M L omega) := by
  apply RegCoeffField.ext
  intro x
  change Matrix.transpose
      (scalarMatrix (d := d)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega ((3 : ℝ) ^ k • x))) =
    scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega ((3 : ℝ) ^ k • x))
  exact scalarMatrix_isSymm _

private theorem restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube'
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) (omega : Sample d) :
    Ch04.restrictionResponseJObservableCubeSet R p q
        (aCutoffRegCoeffField M L omega) =
      cutoffResponseOnCube M L p q R omega := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d116_restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube (d := d) (M := M) (L := L) (p := p) (q := q) (R := R) (omega := omega)

private theorem restrictionResponseJObservableCubeSet_eq_ch02_responseJ
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q : Vec d) :
    Ch04.restrictionResponseJObservableCubeSet Q p q a =
      Ch02.responseJ (Ch02.cubeDomain Q)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        p q := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  symm
  calc
    Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q =
        ResponseJ (openCubeSet Q) p q a.toFun := by
      simpa [F, Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
        Ch04.coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using!
        Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
          (Ch02.cubeDomain Q) (F.coeffOn Q) p q
    _ = Ch04.restrictionResponseJObservableCubeSet Q p q a := by
      rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a.toFun]
      rfl

private theorem restrictionResponseJObservableCubeSet_smul'
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (c : ℝ) (p q : Vec d) :
    Ch04.restrictionResponseJObservableCubeSet Q (c • p) (c • q) a =
      c ^ 2 * Ch04.restrictionResponseJObservableCubeSet Q p q a := by
  rw [restrictionResponseJObservableCubeSet_eq_ch02_responseJ ha,
    restrictionResponseJObservableCubeSet_eq_ch02_responseJ ha,
    Ch02.responseJ_smul]

private theorem fullBlockMatrixProbe_combineInvSqrt_inl
    {d : ℕ} (alpha : ℝ) (i : Fin d) :
    Ch05.Section56.fullBlockMatrixProbe (combineInvSqrtNormalizer alpha)
      (Sum.inl i) = (0, 0) := by
  ext j <;> simp [Ch05.Section56.fullBlockMatrixProbe,
    combineInvSqrtNormalizer, ofFullBlockVec]

private theorem fullBlockMatrixProbe_combineSqrt_inl
    {d : ℕ} (alpha : ℝ) (i : Fin d) :
    Ch05.Section56.fullBlockMatrixProbe (combineSqrtNormalizer alpha)
      (Sum.inl i) = (0, 0) := by
  ext j <;> simp [Ch05.Section56.fullBlockMatrixProbe,
    combineSqrtNormalizer, ofFullBlockVec]

private theorem fullBlockMatrixProbe_combineInvSqrt_inr
    {d : ℕ} (alpha : ℝ) (i : Fin d) :
    Ch05.Section56.fullBlockMatrixProbe (combineInvSqrtNormalizer alpha)
      (Sum.inr i) = (0, Real.sqrt alpha • Pi.single i 1) := by
  ext j <;> simp [Ch05.Section56.fullBlockMatrixProbe,
    combineInvSqrtNormalizer, ofFullBlockVec, Pi.single_apply]

private theorem fullBlockMatrixProbe_combineSqrt_inr
    {d : ℕ} (alpha : ℝ) (i : Fin d) :
    Ch05.Section56.fullBlockMatrixProbe (combineSqrtNormalizer alpha)
      (Sum.inr i) = (0, (Real.sqrt alpha)⁻¹ • Pi.single i 1) := by
  ext j <;> simp [Ch05.Section56.fullBlockMatrixProbe,
    combineSqrtNormalizer, ofFullBlockVec, Pi.single_apply]

private theorem blockJTraceCell_combine_inl_eq_zero
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (R : TriadicCube d) (i : Fin d) :
    Ch05.Section56.blockJObservableCubeSetBlockVec R
      (Ch05.Section56.fullBlockMatrixProbe
        (combineInvSqrtNormalizer (ahom M L)) (Sum.inl i))
      (Ch05.Section56.fullBlockMatrixProbe
        (combineSqrtNormalizer (ahom M L)) (Sum.inl i))
      (rescaleReg (aCutoffNormalizationDepth d L)
        (aCutoffRegCoeffField M L omega)) = 0 := by
  let k := aCutoffNormalizationDepth d L
  let a := rescaleReg k (aCutoffRegCoeffField M L omega)
  rw [fullBlockMatrixProbe_combineInvSqrt_inl,
    fullBlockMatrixProbe_combineSqrt_inl]
  unfold Ch05.Section56.blockJObservableCubeSetBlockVec
  rw [Ch04.blockJObservableCubeSet_apply]
  simp only [sub_zero, add_zero]
  rw [show adjointReg a = a by
    simpa [a, k] using! adjointReg_rescale_aCutoff_eq M L k omega]
  have hzero := restrictionResponseJObservableCubeSet_smul'
    (aelocallyUniformlyEllipticField_dilateReg
      (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
      (-(k : ℤ))) R (0 : ℝ) (0 : Vec d) (0 : Vec d)
  have hzero' : Ch04.restrictionResponseJObservableCubeSet R 0 0 a = 0 := by
    simpa [a, Ch04.rescaleReg_eq_dilateReg_neg_nat] using! hzero
  rw [hzero']
  ring

private theorem blockJTraceCell_combine_inr_eq_coordinateLocalResponse
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (R : TriadicCube d) (i : Fin d) :
    Ch05.Section56.blockJObservableCubeSetBlockVec R
      (Ch05.Section56.fullBlockMatrixProbe
        (combineInvSqrtNormalizer (ahom M L)) (Sum.inr i))
      (Ch05.Section56.fullBlockMatrixProbe
        (combineSqrtNormalizer (ahom M L)) (Sum.inr i))
      (rescaleReg (aCutoffNormalizationDepth d L)
        (aCutoffRegCoeffField M L omega)) =
      ahom M L * cutoffResponseOnCube M L
        ((ahom M L)⁻¹ • Pi.single i 1) (Pi.single i 1)
        (Ch02.dilateCube (aCutoffNormalizationDepth d L : ℤ) R) omega := by
  let alpha := ahom M L
  let k := aCutoffNormalizationDepth d L
  let a := rescaleReg k (aCutoffRegCoeffField M L omega)
  have halpha : 0 < alpha := by simpa [alpha] using! ahom_pos M L
  have hsqrt : Real.sqrt alpha * Real.sqrt alpha = alpha :=
    Real.mul_self_sqrt halpha.le
  have hsqrt0 : Real.sqrt alpha ≠ 0 := ne_of_gt (Real.sqrt_pos.2 halpha)
  have hinvSqrt : (Real.sqrt alpha)⁻¹ = Real.sqrt alpha * alpha⁻¹ := by
    calc
      (Real.sqrt alpha)⁻¹ =
          Real.sqrt alpha * (Real.sqrt alpha * Real.sqrt alpha)⁻¹ := by
        field_simp [hsqrt0]
      _ = Real.sqrt alpha * alpha⁻¹ := by rw [hsqrt]
  rw [fullBlockMatrixProbe_combineInvSqrt_inr,
    fullBlockMatrixProbe_combineSqrt_inr]
  unfold Ch05.Section56.blockJObservableCubeSetBlockVec
  rw [Ch04.blockJObservableCubeSet_apply]
  simp only [zero_sub, add_zero, zero_add]
  rw [show adjointReg a = a by
    simpa [a, k] using! adjointReg_rescale_aCutoff_eq M L k omega]
  rw [Ch04.restrictionResponseJObservableCubeSet_rescaleCoeffField_of_aelocallyUniformlyElliptic
      (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega),
    Ch04.restrictionResponseJObservableCubeSet_rescaleCoeffField_of_aelocallyUniformlyElliptic
      (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)]
  change (1 / 2 : ℝ) *
      Ch04.restrictionResponseJObservableCubeSet (Ch02.dilateCube (k : ℤ) R)
        (-((Real.sqrt alpha)⁻¹ • Pi.single i 1))
        (-(Real.sqrt alpha • Pi.single i 1)) (aCutoffRegCoeffField M L omega) +
    (1 / 2 : ℝ) *
      Ch04.restrictionResponseJObservableCubeSet (Ch02.dilateCube (k : ℤ) R)
        ((Real.sqrt alpha)⁻¹ • Pi.single i 1)
        (Real.sqrt alpha • Pi.single i 1) (aCutoffRegCoeffField M L omega) =
    alpha * cutoffResponseOnCube M L
      (alpha⁻¹ • Pi.single i 1) (Pi.single i 1)
      (Ch02.dilateCube (k : ℤ) R) omega
  have hneg := restrictionResponseJObservableCubeSet_smul'
    (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
    (Ch02.dilateCube (k : ℤ) R) (-1 : ℝ)
    ((Real.sqrt alpha)⁻¹ • Pi.single i 1)
    (Real.sqrt alpha • Pi.single i 1)
  simp only [neg_smul, neg_sq, one_pow, one_mul, one_smul] at hneg
  rw [hneg]
  have hscale : Ch04.restrictionResponseJObservableCubeSet
      (Ch02.dilateCube (k : ℤ) R)
      ((Real.sqrt alpha)⁻¹ • Pi.single i 1)
      (Real.sqrt alpha • Pi.single i 1)
      (aCutoffRegCoeffField M L omega) =
    alpha * cutoffResponseOnCube M L
      (alpha⁻¹ • Pi.single i 1) (Pi.single i 1)
      (Ch02.dilateCube (k : ℤ) R) omega := by
    rw [← restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube']
    rw [show (Real.sqrt alpha)⁻¹ • Pi.single i 1 =
        Real.sqrt alpha • (alpha⁻¹ • Pi.single i 1) by
      rw [smul_smul, ← hinvSqrt]]
    exact restrictionResponseJObservableCubeSet_smul'
      (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
      (Ch02.dilateCube (k : ℤ) R) (Real.sqrt alpha)
      (alpha⁻¹ • Pi.single i 1) (Pi.single i 1) |>.trans
        (by rw [Real.sq_sqrt halpha.le])
  rw [hscale]
  dsimp only [alpha]
  ring

/-- A single normalized trace cell is exactly `ahom` times the manuscript's
sum of coordinate responses on the corresponding physical cube. -/
theorem fullBlockJTraceCell_normalized_eq_coordinateLocalResponse_sum
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (R : TriadicCube d) :
    (∑ gamma : BlockCoord d,
      Ch05.Section56.blockJObservableCubeSetBlockVec R
        (Ch05.Section56.fullBlockMatrixProbe
          (combineInvSqrtNormalizer (ahom M L)) gamma)
        (Ch05.Section56.fullBlockMatrixProbe
          (combineSqrtNormalizer (ahom M L)) gamma)
        (rescaleReg (aCutoffNormalizationDepth d L)
          (aCutoffRegCoeffField M L omega))) =
      ahom M L * ∑ i : Fin d,
        cutoffResponseOnCube M L
          ((ahom M L)⁻¹ • Pi.single i 1) (Pi.single i 1)
          (Ch02.dilateCube (aCutoffNormalizationDepth d L : ℤ) R) omega := by
  classical
  rw [Fintype.sum_sum_type, Finset.mul_sum]
  rw [Finset.sum_eq_zero fun i _ => blockJTraceCell_combine_inl_eq_zero M L omega R i,
    zero_add]
  exact Finset.sum_congr rfl fun i _ =>
    blockJTraceCell_combine_inr_eq_coordinateLocalResponse M L omega R i

private theorem descendantsAverage_dilateCube {d : ℕ} (k : ℤ)
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) :
    descendantsAverage (Ch02.dilateCube k Q) j F =
      descendantsAverage Q j (fun R => F (Ch02.dilateCube k R)) := by
  classical
  dsimp [descendantsAverage]
  rw [Ch02.descendantsAtDepth_dilateCube]
  rw [Finset.card_image_of_injective _ (Ch02.dilateCube_injective k)]
  rw [Finset.sum_image]
  intro R _hR S _hS hRS
  exact Ch02.dilateCube_injective k hRS

private theorem descendantsAverage_const_mul {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ) (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => c * F R) =
      c * descendantsAverage Q j F := by
  classical
  unfold descendantsAverage
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _hR
  ring

/-- **Identification 2.**  The lower-right entry of the normalized descendant
full-block average is `ahom` times the literal finite dual average on the
physical descendants. -/
theorem descendantsAverageFluctuation_lowerRight_eq_literalDualAverage
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (n : ℤ) (Q : TriadicCube d) (jdepth : ℕ)
    (i j : Fin d) :
    Ch05.Section56.descendantsAverageFluctuationMatrixWithNormalizer
      ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
        (aCutoffNormalizationDepth d L))
      (aCutoffNormalization_structuralLaw M L)
      (n - (aCutoffNormalizationDepth d L : ℤ))
      (combineInvSqrtNormalizer (ahom M L)) Q jdepth
      (rescaleReg (aCutoffNormalizationDepth d L)
        (aCutoffRegCoeffField M L omega))
      (Sum.inr i) (Sum.inr j) =
      ahom M L * descendantsAverage
        (Ch02.dilateCube (aCutoffNormalizationDepth d L : ℤ) Q) jdepth
        (fun R =>
          (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j -
            abarStarInv M L (Ch02.cubeDomain (originCube d n)) i j) := by
  unfold Ch05.Section56.descendantsAverageFluctuationMatrixWithNormalizer
    Ch05.Section56.descendantsAverageFullBlockMat
  rw [descendantsAverage_dilateCube]
  rw [← descendantsAverage_const_mul]
  apply congrArg (descendantsAverage Q jdepth)
  funext R
  exact fullBlockFluctuation_lowerRight_eq_centered_randomAStarInv_dilateCube
    M L omega n R i j

/-- **Identification 3 before squaring.**  The Chapter 5 trace average on the
normalized cube is the literal coordinate-response average on its physical
dilate, with the single gauge factor `ahom`. -/
theorem blockJTraceAverageWithNormalizers_normalized_eq
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) (j : ℕ) :
    Ch05.Section56.blockJTraceAverageWithNormalizers
      (combineInvSqrtNormalizer (ahom M L))
      (combineSqrtNormalizer (ahom M L)) Q j
      (rescaleReg (aCutoffNormalizationDepth d L)
        (aCutoffRegCoeffField M L omega)) =
      ahom M L * descendantsAverage
        (Ch02.dilateCube (aCutoffNormalizationDepth d L : ℤ) Q) j
        (fun R => ∑ i : Fin d, cutoffResponseOnCube M L
          ((ahom M L)⁻¹ • Pi.single i 1) (Pi.single i 1) R omega) := by
  unfold Ch05.Section56.blockJTraceAverageWithNormalizers
  rw [descendantsAverage_dilateCube]
  rw [← descendantsAverage_const_mul]
  apply congrArg (descendantsAverage Q j)
  funext R
  exact fullBlockJTraceCell_normalized_eq_coordinateLocalResponse_sum
    M L omega R

/-- **Identification 3.**  Squared form consumed by the two-plus-eight
endpoint. -/
theorem blockJTraceAverageSqWithNormalizers_normalized_eq
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) (j : ℕ) :
    Ch05.Section56.blockJTraceAverageSqWithNormalizers
      (combineInvSqrtNormalizer (ahom M L))
      (combineSqrtNormalizer (ahom M L)) Q j
      (rescaleReg (aCutoffNormalizationDepth d L)
        (aCutoffRegCoeffField M L omega)) =
      (ahom M L) ^ 2 *
        (descendantsAverage
          (Ch02.dilateCube (aCutoffNormalizationDepth d L : ℤ) Q) j
          (fun R => ∑ i : Fin d, cutoffResponseOnCube M L
            ((ahom M L)⁻¹ • Pi.single i 1) (Pi.single i 1) R omega)) ^ 2 := by
  unfold Ch05.Section56.blockJTraceAverageSqWithNormalizers
  rw [blockJTraceAverageWithNormalizers_normalized_eq]
  ring

/-! ## Whole-matrix moment budget (the polarization/off-diagonal seam) -/

/-- The sharp-comparison estimate controls the whole normalized inverse-star
matrix, not only its diagonal entries. -/
theorem matrixOperatorNorm_ahom_smul_randomAStarInv_sub_one_sq_le_normalizedDefect
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (omega : Sample d) :
    Ch02.matrixOperatorNorm
        (ahom M L • (randomAStarMatrix M L U omega)⁻¹ - 1) ^ 2 ≤
      10 * (normalizedDefect M L U omega).toReal *
        (1 + (normalizedDefect M L U omega).toReal) := by
  classical
  let a := (aCutoffCoeffOnData M L omega U).toCoeffOn
  let alpha := ahom M L
  let b : Mat d := scalarMatrix (d := d) alpha
  let Astar := aStarMatrix U a
  let H := sharpResponseSup U a b
  let D := (normalizedDefect M L U omega).toReal
  have halpha : 0 < alpha := by simpa [alpha] using! ahom_pos M L
  have hb : b.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (scalarMatrix_isSymm alpha) ?_
    intro x hx
    have hxpos : 0 < vecNormSq x :=
      lt_of_le_of_ne (vecNormSq_nonneg x)
        (by simpa [vecNormSq_eq_zero_iff, eq_comm] using! hx)
    change 0 < vecDot x (matVecMul b x)
    rw [show matVecMul b x = alpha • x by
      simpa [b] using! matVecMul_scalarMatrix alpha x]
    simpa [vecDot_smul_right, vecNormSq] using! mul_pos halpha hxpos
  have hsqrt : matrixSqrt b = Real.sqrt alpha • (1 : Mat d) := by
    dsimp [matrixSqrt]
    apply CFC.sqrt_unique
    · calc
        (Real.sqrt alpha • (1 : Mat d)) *
              (Real.sqrt alpha • (1 : Mat d)) =
            (Real.sqrt alpha * Real.sqrt alpha) • ((1 : Mat d) * 1) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = alpha • (1 : Mat d) := by
          rw [one_mul, Real.mul_self_sqrt halpha.le]
        _ = b := rfl
    · rw [Matrix.nonneg_iff_posSemidef]
      exact Matrix.PosSemidef.one.smul (Real.sqrt_nonneg alpha)
  have hmatrix : matrixSqrt b * Astar⁻¹ * matrixSqrt b - 1 =
      alpha • Astar⁻¹ - 1 := by
    rw [hsqrt, Matrix.smul_mul, Matrix.mul_smul]
    simp only [one_mul, mul_one]
    rw [smul_smul, Real.mul_self_sqrt halpha.le]
  have hdev := sharpCompareJ_matrix_deviations U a
    (aCutoffCoeffOnData M L omega U).isSymmetric b hb
  have hterm : Ch02.matrixOperatorNorm (alpha • Astar⁻¹ - 1) ^ 2 ≤
      10 * H * (1 + H) := by
    rw [hmatrix] at hdev
    have hfirst : 0 ≤ Ch02.matrixOperatorNorm
        (matrixInvSqrt b * (aMatrix U a - Astar) * matrixInvSqrt b) :=
      Ch02.matrixOperatorNorm_nonneg _
    have hthird : 0 ≤ Ch02.matrixOperatorNorm
        (matrixInvSqrt b * aMatrix U a * matrixInvSqrt b - 1) ^ 2 := sq_nonneg _
    linarith
  have hHD : H = D := by
    simpa [H, D, a, b, alpha] using!
      sharpResponseSup_scalarMatrix_eq_normalizedDefect_toReal M L U omega
  rw [hHD] at hterm
  simpa [alpha, Astar, D, randomAStarMatrix] using! hterm

/-- Every entry, including off-diagonal entries, inherits the normalized
operator defect bound.  This is the coordinate/polarization endpoint used by
the finite coloring. -/
theorem sq_randomAStarInv_entry_sub_scalar_le_normalizedDefect
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (omega : Sample d) (i j : Fin d) :
    ((randomAStarMatrix M L U omega)⁻¹ i j -
        (ahom M L)⁻¹ * (1 : Mat d) i j) ^ 2 ≤
      10 * (ahom M L)⁻¹ ^ 2 *
        (normalizedDefect M L U omega).toReal *
          (1 + (normalizedDefect M L U omega).toReal) := by
  let alpha := ahom M L
  let Z : Mat d := alpha • (randomAStarMatrix M L U omega)⁻¹ - 1
  have halpha : 0 < alpha := by simpa [alpha] using! ahom_pos M L
  have hentry : |Z i j| ≤ Ch02.matrixOperatorNorm Z :=
    Ch02.abs_entry_le_matrixOperatorNorm Z i j
  have hentryEq :
      (randomAStarMatrix M L U omega)⁻¹ i j - alpha⁻¹ * (1 : Mat d) i j =
        alpha⁻¹ * Z i j := by
    dsimp only [Z]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply, ite_true]
      field_simp [halpha.ne']
    · simp only [Matrix.one_apply, hij, ite_false, mul_zero, sub_zero]
      field_simp [halpha.ne']
  have hsq : (alpha⁻¹ * Z i j) ^ 2 ≤
      alpha⁻¹ ^ 2 * Ch02.matrixOperatorNorm Z ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      (by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hentry 2)
      (sq_nonneg _)
  have hop := matrixOperatorNorm_ahom_smul_randomAStarInv_sub_one_sq_le_normalizedDefect
    M L U omega
  have hscaled := mul_le_mul_of_nonneg_left hop (sq_nonneg alpha⁻¹)
  rw [hentryEq]
  dsimp only [Z, alpha] at hsq hscaled ⊢
  nlinarith

/-- Uniform `L²` budget for every centered inverse-star entry on a scale-`L`
cube.  The diagonal case recovers P-53; the off-diagonal case is the needed
polarization/Frobenius extension. -/
theorem randomAStarInv_entry_sub_scalar_integral_sq_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (Q : TriadicCube d) (hQ : Q.scale = (L : ℤ)) (i j : Fin d) :
    ∫ omega,
        ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j -
          (ahom M L)⁻¹ * (1 : Mat d) i j) ^ 2 ∂M.P.toMeasure ≤
      20 * (ahom M L)⁻¹ ^ 2 * delta1 := by
  let U := Ch02.cubeDomain Q
  let D : Sample d → ℝ := fun omega =>
    (normalizedDefect M L U omega).toReal
  let Y : Sample d → ℝ := fun omega =>
    (randomAStarMatrix M L U omega)⁻¹ i j -
      (ahom M L)⁻¹ * (1 : Mat d) i j
  have hD := normalizedDefect_toReal_moment_budgets
    M hxi hS le_rfl hLm0 Q hQ
  have hDmem : MemLp D 2 M.P.toMeasure := by simpa [D, U] using! hD.1
  have hDint : Integrable D M.P.toMeasure := hDmem.integrable one_le_two
  have hDsq : Integrable (fun omega => D omega ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hDmem.aestronglyMeasurable).1 hDmem
  have hrawMeas : AEStronglyMeasurable (fun omega : Sample d =>
      (randomAStarMatrix M L U omega)⁻¹ i j) M.P.toMeasure :=
    ((((integrable_randomAStarMatrix_inv M L U).eval i).eval j).1)
  have hrawMem : MemLp (fun omega : Sample d =>
      (randomAStarMatrix M L U omega)⁻¹ i j) 2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hrawMeas).2
      (integrable_randomAStarInv_entry_sq M L U i j)
  have hYmem : MemLp Y 2 M.P.toMeasure :=
    hrawMem.sub (memLp_const _)
  have hYsq : Integrable (fun omega => Y omega ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hYmem.aestronglyMeasurable).1 hYmem
  have hRhs : Integrable (fun omega =>
      10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega))
      M.P.toMeasure := by
    have heq : (fun omega =>
        10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega)) =
        fun omega => 10 * (ahom M L)⁻¹ ^ 2 * (D omega + D omega ^ 2) := by
      funext omega
      ring
    rw [heq]
    exact (hDint.add hDsq).const_mul _
  have hpoint : ∀ omega, Y omega ^ 2 ≤
      10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega) := by
    intro omega
    simpa [Y, D, U] using!
      sq_randomAStarInv_entry_sub_scalar_le_normalizedDefect
        M L U omega i j
  have hraw : ∫ omega, Y omega ^ 2 ∂M.P.toMeasure ≤
      ∫ omega, 10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega)
        ∂M.P.toMeasure := integral_mono hYsq hRhs hpoint
  have hDfirst : ∫ omega, D omega ∂M.P.toMeasure ≤ delta1 := by
    simpa [D, U] using! hD.2.1
  have hDsecond : ∫ omega, D omega ^ 2 ∂M.P.toMeasure ≤ delta1 ^ 2 := by
    simpa [D, U] using! hD.2.2
  have hraw' : ∫ omega, Y omega ^ 2 ∂M.P.toMeasure ≤
      10 * (ahom M L)⁻¹ ^ 2 *
        ((∫ omega, D omega ∂M.P.toMeasure) +
          ∫ omega, D omega ^ 2 ∂M.P.toMeasure) := by
    calc
      ∫ omega, Y omega ^ 2 ∂M.P.toMeasure ≤
          ∫ omega, 10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega)
            ∂M.P.toMeasure := hraw
      _ = 10 * (ahom M L)⁻¹ ^ 2 *
          ((∫ omega, D omega ∂M.P.toMeasure) +
            ∫ omega, D omega ^ 2 ∂M.P.toMeasure) := by
        rw [show (fun omega =>
            10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega)) =
            fun omega => 10 * (ahom M L)⁻¹ ^ 2 *
              (D omega + D omega ^ 2) by funext omega; ring,
          integral_const_mul, integral_add hDint hDsq]
  have hdelta0 : 0 ≤ delta1 := hS.2.1.le
  have hdelta1 : delta1 ≤ 1 := hS.2.2.1.le
  dsimp only [Y, U] at hraw' ⊢
  nlinarith [mul_nonneg (sq_nonneg (ahom M L)⁻¹)
    (sub_nonneg.mpr hdelta1)]

/-- A positively-thickened local representative of a literal inverse-star
entry.  This is the matrix analogue of the response representative used by
the verified P-52 route: restriction locality is pulled through the cutoff
law and then enlarged to `LocalSigmaR` using! continuity of the carrier. -/
theorem exists_randomAStarInv_entry_thickenedLocal_ae_eq
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (R : TriadicCube d) (i j : Fin d) :
    ∃ Y : Sample d → ℝ,
      @Measurable (Sample d) ℝ
        ((LocalSigmaR
          (Metric.thickening
            (SubdiffusiveProcess.CoarseGrainingVocab.responseRestrictionBridgeRadius d)
            (cubeSet R))).comap
            (aCutoffRegCoeffField M L)) _ Y ∧
      (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
        =ᵐ[M.P.toMeasure] Y := by
  let P := aCutoffRestrictionLaw M L
  let A := aCutoffRegCoeffField M L
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_lowerRight_apply_cubeSet
      R i j with ⟨Y0, hY0local, hY0eq⟩
  let Y : Sample d → ℝ := Y0 ∘ A
  refine ⟨Y, ?_, ?_⟩
  · have hcomp : @Measurable (Sample d) ℝ
        ((RestrictionSigmaR (cubeSet R) (measurableSet_cubeSet R)).comap A) _ Y := by
      exact hY0local.comp (Measurable.of_comap_le le_rfl)
    exact hcomp.mono
      (comap_restrictionSigmaR_le_comap_localSigmaR_thickening A
        (fun omega u v =>
          SubdiffusiveProcess.CoarseGrainingVocab.continuous_aCutoffRegCoeffField_entry_for_response
          M L omega u v)
        (cubeSet R) (measurableSet_cubeSet R)
        (SubdiffusiveProcess.CoarseGrainingVocab.responseRestrictionBridgeRadius d)
        (SubdiffusiveProcess.CoarseGrainingVocab.responseRestrictionBridgeRadius_pos d)) le_rfl
  · have hpull :
        (fun omega : Sample d =>
          (coarseBlockMatrix (cubeSet R) (A omega).toFun).lowerRight i j)
          =ᵐ[M.P.toMeasure] Y := by
      exact ae_eq_comp (measurable_aCutoffRegCoeffField M L).aemeasurable
        (by simpa [P, aCutoffRestrictionLaw_eq_map, Y, A] using! hY0eq)
    filter_upwards [hpull] with omega homega
    dsimp only [A] at homega
    rw [← coarseBlockMatrix_aCutoff_lowerRight_eq_randomAStarInv M L omega R]
    exact homega

/-- The P-36 colored-variance estimate with the P-52 a.e.-local carrier.
This avoids asserting false pointwise `LocalSigmaR` measurability for the
totalized variational observables. -/
theorem variance_probabilityDescendantAverage_le_of_ae_thickenedLocal
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) (hLn : L ≤ n)
    (X : TriadicCube d → Sample d → ℝ) {B : ℝ}
    (hB : 0 ≤ B)
    (hXlocal : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      ∃ Y : Sample d → ℝ,
        @Measurable (Sample d) ℝ
          ((LocalSigmaR
            (Metric.thickening
              (SubdiffusiveProcess.CoarseGrainingVocab.responseRestrictionBridgeRadius d)
              (cubeSet R))).comap (aCutoffRegCoeffField M L)) _ Y ∧
        X R =ᵐ[M.P.toMeasure] Y)
    (hXLp : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      MemLp (X R) 2 M.P.toMeasure)
    (hsecond : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (L : ℤ),
      ∫ omega, (X R omega) ^ 2 ∂M.P.toMeasure ≤ B) :
    variance (probabilityFinsetAverage
      (descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)) X) M.P.toMeasure ≤
      ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
        Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) * B := by
  let s := descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)
  have hs : s.Nonempty := by
    have hscale : (L : ℤ) ≤ (originCube d (n : ℤ)).scale := by
      change (L : ℤ) ≤ (n : ℤ)
      exact_mod_cast hLn
    dsimp only [s]
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (n : ℤ)) hscale]
    exact descendantsAtDepth_nonempty _ _
  have hindep : ∀ c ∈ s.image cubeFreshShellColor,
      Set.Pairwise ↑(s.filter (fun R => cubeFreshShellColor R = c))
        (fun R S => IndepFun (X R) (X S) M.P.toMeasure) := by
    intro c _hc R hR S hS hRS
    have hmut :=
      SubdiffusiveProcess.CoarseGrainingVocab.iIndepFun_cutoff_descendants_colorClass_of_ae_thickenedLocal
        M L L n le_rfl c X (by simpa only [s] using! hXlocal)
    let R' : {Q : TriadicCube d // Q ∈ s.filter
        (fun T => cubeFreshShellColor T = c)} := ⟨R, hR⟩
    let S' : {Q : TriadicCube d // Q ∈ s.filter
        (fun T => cubeFreshShellColor T = c)} := ⟨S, hS⟩
    have hne : R' ≠ S' := by
      intro heq
      exact hRS (congrArg Subtype.val heq)
    exact hmut.indepFun hne
  have hvar := variance_probabilityFinsetAverage_le_of_coloring_secondMoment
    s hs cubeFreshShellColor (by simpa only [s] using! hXLp) hindep
      (by simpa only [s] using! hsecond)
  exact hvar.trans (mul_le_mul_of_nonneg_right
    (freshShellColor_ratio_descendantsAtScale_le hLn) hB)

/-- Colored variance of one literal inverse-star descendant average, centered
at the annealed matrix on the parent scale.  The constant `48` consists of
twice the whole-entry sharp-comparison budget `20` and twice the annealed
mean-defect budget `4`, using! `delta₁ ≤ 1`. -/
theorem variance_descendantAverage_centered_randomAStarInv_entry_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (i j : Fin d) :
    let X : TriadicCube d → Sample d → ℝ := fun R omega =>
      (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j -
        abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j
    variance (probabilityFinsetAverage
      (descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)) X) M.P.toMeasure ≤
      ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
        Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) *
          (48 * (ahom M L)⁻¹ ^ 2 * delta1) := by
  dsimp only
  let b : ℝ := abarStarInv M L
    (Ch02.cubeDomain (originCube d (n : ℤ))) i j
  let s : ℝ := (ahom M L)⁻¹ * (1 : Mat d) i j
  let X : TriadicCube d → Sample d → ℝ := fun R omega =>
    (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j - b
  have hdelta0 : 0 ≤ delta1 := hS.2.1.le
  have hdelta1 : delta1 ≤ 1 := hS.2.2.1.le
  apply variance_probabilityDescendantAverage_le_of_ae_thickenedLocal
    M L n hLn X
  · positivity
  · intro R hR
    rcases exists_randomAStarInv_entry_thickenedLocal_ae_eq M L R i j with
      ⟨Y, hYlocal, hYeq⟩
    refine ⟨fun omega => Y omega - b, hYlocal.sub measurable_const, ?_⟩
    exact hYeq.sub (Filter.EventuallyEq.rfl)
  · intro R _hR
    have hrawMeas : AEStronglyMeasurable (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
        M.P.toMeasure :=
      ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)).eval i).eval j).1)
    have hraw : MemLp (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
        2 M.P.toMeasure :=
      (memLp_two_iff_integrable_sq hrawMeas).2
        (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain R) i j)
    exact hraw.sub (memLp_const _)
  · intro R hR
    have hRscale : R.scale = (L : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    let Z : Sample d → ℝ := fun omega =>
      (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j - s
    have hZmem : MemLp Z 2 M.P.toMeasure := by
      have hrawMeas : AEStronglyMeasurable (fun omega : Sample d =>
          (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
          M.P.toMeasure :=
        ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)).eval i).eval j).1)
      have hraw : MemLp (fun omega : Sample d =>
          (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
          2 M.P.toMeasure :=
        (memLp_two_iff_integrable_sq hrawMeas).2
          (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain R) i j)
      exact hraw.sub (memLp_const _)
    have hXmem : MemLp (X R) 2 M.P.toMeasure := by
      have hrawMeas : AEStronglyMeasurable (fun omega : Sample d =>
          (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
          M.P.toMeasure :=
        ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)).eval i).eval j).1)
      have hraw : MemLp (fun omega : Sample d =>
          (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
          2 M.P.toMeasure :=
        (memLp_two_iff_integrable_sq hrawMeas).2
          (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain R) i j)
      exact hraw.sub (memLp_const _)
    have hZsq : Integrable (fun omega => Z omega ^ 2) M.P.toMeasure :=
      (memLp_two_iff_integrable_sq hZmem.aestronglyMeasurable).1 hZmem
    have hXsq : Integrable (fun omega => X R omega ^ 2) M.P.toMeasure :=
      (memLp_two_iff_integrable_sq hXmem.aestronglyMeasurable).1 hXmem
    have hmean : (s - b) ^ 2 ≤ 4 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
      by_cases hij : i = j
      · subst j
        have hmeanDiag :=
          sq_abs_abarStarInv_entry_sub_ahom_inv_le_of_inductionHypothesis
            M hS hLm0 hLn i
        simp only [sq_abs] at hmeanDiag
        dsimp only [s, b]
        simp only [Matrix.one_apply, ite_true, mul_one]
        nlinarith
      · have hb0 := abarStarInv_originCube_offdiag_eq_zero M L n i j hij
        simp [s, b, hij, hb0]
        positivity
    have hpoint : ∀ omega, X R omega ^ 2 ≤
        2 * Z omega ^ 2 + 2 * (s - b) ^ 2 := by
      intro omega
      dsimp only [X, Z]
      have hsq := sq_nonneg
        (((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j - s) -
          (s - b))
      nlinarith
    have hint : ∫ omega, X R omega ^ 2 ∂M.P.toMeasure ≤
        2 * ∫ omega, Z omega ^ 2 ∂M.P.toMeasure + 2 * (s - b) ^ 2 := by
      calc
        _ ≤ ∫ omega, (2 * Z omega ^ 2 + 2 * (s - b) ^ 2)
            ∂M.P.toMeasure := integral_mono hXsq
              ((hZsq.const_mul _).add (integrable_const _)) hpoint
        _ = _ := by
          rw [integral_add (hZsq.const_mul _) (integrable_const _),
            integral_const_mul, integral_const, probReal_univ, one_smul]
    have hZbound := randomAStarInv_entry_sub_scalar_integral_sq_le
      M hxi hS hLm0 R hRscale i j
    calc
      _ ≤ 2 * ∫ omega, Z omega ^ 2 ∂M.P.toMeasure + 2 * (s - b) ^ 2 := hint
      _ ≤ 2 * (20 * (ahom M L)⁻¹ ^ 2 * delta1) +
          2 * (4 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by gcongr
      _ ≤ 48 * (ahom M L)⁻¹ ^ 2 * delta1 := by
        nlinarith [mul_nonneg (sq_nonneg (ahom M L)⁻¹)
          (mul_nonneg hdelta0 (sub_nonneg.mpr hdelta1))]

/-- **Identification 4a.**  Coordinate/Frobenius aggregation of the literal
descendant matrix variation into the first vector quadratic observable of the
P-57 expectation apex. -/
theorem ahom_mul_coarseMatrixVariationSq_aCutoff_le_entry_sum
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q R : TriadicCube d) (p q : Vec d)
    (hqNorm : vecNormSq q ≤ ahom M L) :
    ahom M L *
      coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
        Q p q R ≤
      (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
        ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j -
          (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j) ^ 2 := by
  rw [coarseMatrixVariationSq_aCutoff_eq]
  let X : Mat d :=
    (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ -
      (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹
  have hvec := Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq X q
  have halpha : 0 ≤ ahom M L := (ahom_pos M L).le
  have hscaled := mul_le_mul_of_nonneg_left hvec halpha
  have hinner := mul_le_mul_of_nonneg_left hqNorm
    (Ch02.matrixFrobeniusNormSq_nonneg X)
  calc
    _ ≤ ahom M L * (Ch02.matrixFrobeniusNormSq X * vecNormSq q) := hscaled
    _ ≤ ahom M L * (Ch02.matrixFrobeniusNormSq X * ahom M L) :=
      mul_le_mul_of_nonneg_left hinner halpha
    _ = _ := by
      unfold Ch02.matrixFrobeniusNormSq
      dsimp only [X]
      simp only [Matrix.sub_apply]
      ring

/-- **Identification 4b.**  Under the headline relation `q = ahom_L p`, the
second vector quadratic observable is bounded by the Frobenius sum of the
deviation from the scalar reference matrix. -/
theorem ahom_mul_vecNormSq_coarseScaleSeparation_aCutoff_le_entry_sum
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) (p q : Vec d)
    (hq : q = ahom M L • p) (hqNorm : vecNormSq q ≤ ahom M L) :
    ahom M L * vecNormSq
      (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
        Q p q) ≤
      (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
        ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j -
          (ahom M L)⁻¹ * (1 : Mat d) i j) ^ 2 := by
  let alpha := ahom M L
  let A : Mat d := (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹
  let X : Mat d := A - alpha⁻¹ • (1 : Mat d)
  have halpha : 0 < alpha := by simpa [alpha] using! ahom_pos M L
  have hp : p = alpha⁻¹ • q := by
    rw [hq]
    ext i
    simp [alpha, halpha.ne']
  have hsep : coarseScaleSeparation (aCutoffRegCoeffField M L omega)
      (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
      Q p q = matVecMul X q := by
    have hone : matVecMul (1 : Mat d) q = q := by
      funext i
      simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
    rw [coarseScaleSeparation_aCutoff_eq_randomAStarInv_mulVec_sub, hp]
    dsimp only [X]
    rw [sub_matVecMul, smul_matVecMul, hone]
  rw [hsep]
  have hvec := Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq X q
  have hscaled := mul_le_mul_of_nonneg_left hvec halpha.le
  have hinner := mul_le_mul_of_nonneg_left hqNorm
    (Ch02.matrixFrobeniusNormSq_nonneg X)
  calc
    _ ≤ alpha * (Ch02.matrixFrobeniusNormSq X * vecNormSq q) := hscaled
    _ ≤ alpha * (Ch02.matrixFrobeniusNormSq X * alpha) :=
      mul_le_mul_of_nonneg_left hinner halpha.le
    _ = _ := by
      unfold Ch02.matrixFrobeniusNormSq
      dsimp only [X, A, alpha]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring

/-! ## Coordinate/Frobenius aggregation -/

private theorem fullBlockOperatorNormSq_le_sum_sq {d : ℕ}
    (X : FullBlockMat d) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ ^ 2 ≤
      ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d, X alpha beta ^ 2 := by
  let S : ℝ := ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d, X alpha beta ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  let T := Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X
  have hT : ‖T‖ ≤ Real.sqrt S := by
    refine T.opNorm_le_bound (Real.sqrt_nonneg S) ?_
    intro x
    let v : FullBlockVec d := x.ofLp
    have hxnorm : ‖x‖ ^ 2 = ∑ beta : BlockCoord d, (v beta) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [v, Real.norm_eq_abs, sq_abs]
    have hTxnorm : ‖T x‖ ^ 2 =
        ∑ alpha : BlockCoord d,
          (∑ beta : BlockCoord d, X alpha beta * v beta) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [T, v, Matrix.mulVec, dotProduct,
        Real.norm_eq_abs, sq_abs]
    have hcs : ∀ alpha : BlockCoord d,
        (∑ beta : BlockCoord d, X alpha beta * v beta) ^ 2 ≤
          (∑ beta : BlockCoord d, X alpha beta ^ 2) *
            ∑ beta : BlockCoord d, v beta ^ 2 := by
      intro alpha
      simpa using! Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun beta => X alpha beta) v
    have hsq : ‖T x‖ ^ 2 ≤ S * ‖x‖ ^ 2 := by
      rw [hTxnorm, hxnorm]
      calc
        ∑ alpha : BlockCoord d,
            (∑ beta : BlockCoord d, X alpha beta * v beta) ^ 2 ≤
            ∑ alpha : BlockCoord d,
              ((∑ beta : BlockCoord d, X alpha beta ^ 2) *
                ∑ beta : BlockCoord d, v beta ^ 2) :=
          Finset.sum_le_sum fun alpha _ => hcs alpha
        _ = S * ∑ beta : BlockCoord d, v beta ^ 2 := by
          rw [Finset.sum_mul]
    have hrhs : (Real.sqrt S * ‖x‖) ^ 2 = S * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hS]
    have hsq' : ‖T x‖ ^ 2 ≤ (Real.sqrt S * ‖x‖) ^ 2 := by
      rw [hrhs]
      exact hsq
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg S)
      (norm_nonneg x))).mp hsq'
  have hsq := pow_le_pow_left₀ (norm_nonneg T) hT 2
  rw [Real.sq_sqrt hS] at hsq
  simpa [T, S] using! hsq

private theorem abs_fullBlock_entry_le_operatorNorm {d : ℕ}
    (X : FullBlockMat d) (alpha beta : BlockCoord d) :
    |X alpha beta| ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ := by
  let e : EuclideanSpace ℝ (BlockCoord d) :=
    WithLp.toLp 2 (Pi.single beta (1 : ℝ))
  have hcoord :
      ‖(Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X e).ofLp alpha‖ ≤
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X e‖ :=
    PiLp.norm_apply_le _ alpha
  have hop :
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X e‖ ≤
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ * ‖e‖ :=
    (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X).le_opNorm e
  have he : ‖e‖ = 1 := by simp [e]
  have hentry :
      ‖(Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X e).ofLp alpha‖ =
        |X alpha beta| := by
    simp [e, Real.norm_eq_abs, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec]
  calc
    |X alpha beta| =
        ‖(Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X e).ofLp alpha‖ :=
      hentry.symm
    _ ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X e‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ * ‖e‖ := hop
    _ = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ := by rw [he, mul_one]

/-- **Identification 1, coordinate lower bound.**  Every literal centered
inverse-star entry, including the polarized off-diagonal entries, is bounded
by the normalized parent full-block operator fluctuation. -/
theorem sq_ahom_mul_centered_randomAStarInv_entry_le_fullBlockFluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (n : ℤ) (i j : Fin d) :
    (ahom M L *
      ((randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d n)) omega)⁻¹ i j -
        abarStarInv M L (Ch02.cubeDomain (originCube d n)) i j)) ^ 2 ≤
      Ch05.Section56.fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
        ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
          (aCutoffNormalizationDepth d L))
        (aCutoffNormalization_structuralLaw M L)
        (n - (aCutoffNormalizationDepth d L : ℤ))
        (combineInvSqrtNormalizer (ahom M L))
        (originCube d (n - (aCutoffNormalizationDepth d L : ℤ)))
        (rescaleReg (aCutoffNormalizationDepth d L)
          (aCutoffRegCoeffField M L omega)) := by
  let X := Ch05.Section56.fullBlockFluctuationMatrixWithNormalizer
    ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
      (aCutoffNormalizationDepth d L))
    (aCutoffNormalization_structuralLaw M L)
    (n - (aCutoffNormalizationDepth d L : ℤ))
    (combineInvSqrtNormalizer (ahom M L))
    (cubeSet (originCube d (n - (aCutoffNormalizationDepth d L : ℤ))))
    (rescaleReg (aCutoffNormalizationDepth d L)
      (aCutoffRegCoeffField M L omega))
  have hentry := abs_fullBlock_entry_le_operatorNorm X (Sum.inr i) (Sum.inr j)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hentry 2
  have hread := fullBlockFluctuation_lowerRight_eq_centered_randomAStarInv
    M L omega n i j
  unfold Ch05.Section56.fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
    Ch05.Section56.fullBlockFluctuationOperatorNormSqWithNormalizer
  change (ahom M L * _) ^ 2 ≤
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ ^ 2
  rw [← hread]
  simpa [sq_abs] using! hsq

private theorem fullBlockFluctuation_apply_eq_zero_of_not_lowerRight
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (center : ℤ) (U : Set (Vec d)) (a : RegCoeffField d)
    (alpha beta : BlockCoord d)
    (h : (∀ i, alpha ≠ Sum.inr i) ∨ (∀ j, beta ≠ Sum.inr j)) :
    Ch05.Section56.fullBlockFluctuationMatrixWithNormalizer
        ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
          (aCutoffNormalizationDepth d L))
        (aCutoffNormalization_structuralLaw M L) center
        (combineInvSqrtNormalizer (ahom M L)) U a alpha beta = 0 := by
  rw [Ch05.Section56.fullBlockFluctuationMatrixWithNormalizer,
    transpose_combineInvSqrtNormalizer]
  unfold combineInvSqrtNormalizer
  rw [diagonal_mul_mul_diagonal_apply]
  rcases alpha with i | i
  · simp
  · rcases beta with j | j
    · simp
    · exact (h.elim (fun hleft => (hleft i rfl).elim)
        (fun hright => (hright j rfl).elim))

private theorem descendantsAverageFluctuation_apply_eq_zero_of_not_lowerRight
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (center : ℤ) (Q : TriadicCube d) (jdepth : ℕ) (a : RegCoeffField d)
    (alpha beta : BlockCoord d)
    (h : (∀ i, alpha ≠ Sum.inr i) ∨ (∀ j, beta ≠ Sum.inr j)) :
    Ch05.Section56.descendantsAverageFluctuationMatrixWithNormalizer
        ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
          (aCutoffNormalizationDepth d L))
        (aCutoffNormalization_structuralLaw M L) center
        (combineInvSqrtNormalizer (ahom M L)) Q jdepth a alpha beta = 0 := by
  unfold Ch05.Section56.descendantsAverageFluctuationMatrixWithNormalizer
    Ch05.Section56.descendantsAverageFullBlockMat descendantsAverage
  simp_rw [fullBlockFluctuation_apply_eq_zero_of_not_lowerRight
    M L center (cubeSet _) a alpha beta h]
  simp

/-- The projected descendant full-block norm is controlled by the Frobenius
sum of its literal lower-right entries.  Combined with Identification 2 this
is the coordinate aggregation needed by the finite-color variance estimate. -/
theorem descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_lowerRight_sum
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (center : ℤ) (Q : TriadicCube d) (jdepth : ℕ) (a : RegCoeffField d) :
    Ch05.Section56.descendantsAverageFluctuationOperatorNormSqWithNormalizer
        ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
          (aCutoffNormalizationDepth d L))
        (aCutoffNormalization_structuralLaw M L) center
        (combineInvSqrtNormalizer (ahom M L)) Q jdepth a ≤
      ∑ i : Fin d, ∑ j : Fin d,
        (Ch05.Section56.descendantsAverageFluctuationMatrixWithNormalizer
          ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
            (aCutoffNormalizationDepth d L))
          (aCutoffNormalization_structuralLaw M L) center
          (combineInvSqrtNormalizer (ahom M L)) Q jdepth a
          (Sum.inr i) (Sum.inr j)) ^ 2 := by
  let X := Ch05.Section56.descendantsAverageFluctuationMatrixWithNormalizer
    ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
      (aCutoffNormalizationDepth d L))
    (aCutoffNormalization_structuralLaw M L) center
    (combineInvSqrtNormalizer (ahom M L)) Q jdepth a
  have h := fullBlockOperatorNormSq_le_sum_sq X
  unfold Ch05.Section56.descendantsAverageFluctuationOperatorNormSqWithNormalizer
  change ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ ^ 2 ≤ _
  calc
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ ^ 2 ≤
        ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d, X alpha beta ^ 2 := h
    _ = ∑ i : Fin d, ∑ j : Fin d, X (Sum.inr i) (Sum.inr j) ^ 2 := by
      rw [Fintype.sum_sum_type]
      have hleft : ∑ i : Fin d, ∑ beta : BlockCoord d,
          X (Sum.inl i) beta ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro beta _
        dsimp only [X]
        rw [descendantsAverageFluctuation_apply_eq_zero_of_not_lowerRight
          M L center Q jdepth a (Sum.inl i) beta]
        · norm_num
        · exact Or.inl (fun k hki => by cases hki)
      rw [hleft, zero_add]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_sum_type]
      have hinl : ∑ j : Fin d, X (Sum.inr i) (Sum.inl j) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        dsimp only [X]
        rw [descendantsAverageFluctuation_apply_eq_zero_of_not_lowerRight
          M L center Q jdepth a (Sum.inr i) (Sum.inl j)]
        · norm_num
        · exact Or.inr (fun k hkj => by cases hkj)
      rw [hinl, zero_add]
    _ = _ := rfl

/-- **Identification 2, norm form.**  The descendant full-block operator norm
is bounded by the literal Frobenius sum of all centered inverse-star averages
on the physical dilate. -/
theorem descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_literalDualAverage
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (n : ℤ) (Q : TriadicCube d) (jdepth : ℕ) :
    Ch05.Section56.descendantsAverageFluctuationOperatorNormSqWithNormalizer
        ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
          (aCutoffNormalizationDepth d L))
        (aCutoffNormalization_structuralLaw M L)
        (n - (aCutoffNormalizationDepth d L : ℤ))
        (combineInvSqrtNormalizer (ahom M L)) Q jdepth
        (rescaleReg (aCutoffNormalizationDepth d L)
          (aCutoffRegCoeffField M L omega)) ≤
      (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
        (descendantsAverage
          (Ch02.dilateCube (aCutoffNormalizationDepth d L : ℤ) Q) jdepth
          (fun R =>
            (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j -
              abarStarInv M L (Ch02.cubeDomain (originCube d n)) i j)) ^ 2 := by
  calc
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
        (Ch05.Section56.descendantsAverageFluctuationMatrixWithNormalizer
          ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
            (aCutoffNormalizationDepth d L))
          (aCutoffNormalization_structuralLaw M L)
          (n - (aCutoffNormalizationDepth d L : ℤ))
          (combineInvSqrtNormalizer (ahom M L)) Q jdepth
          (rescaleReg (aCutoffNormalizationDepth d L)
            (aCutoffRegCoeffField M L omega))
          (Sum.inr i) (Sum.inr j)) ^ 2 :=
      descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_lowerRight_sum
        M L _ Q jdepth _
    _ = _ := by
      simp_rw [descendantsAverageFluctuation_lowerRight_eq_literalDualAverage]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- **Identification 4, samplewise coordinate form.**  The Chapter 5
two-plus-eight estimate, transported to the literal cutoff sample and read in
coordinates, controls every centered inverse-star entry by the Frobenius sum
of the literal descendant averages and the squared coordinate-response trace.
This is the exact deterministic input to the finite-color integration. -/
theorem centered_randomAStarInv_entry_sq_le_two_descendantAverage_add_eight_trace_ae
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ)
    (i j : Fin d) :
    (fun omega : Sample d =>
      ((randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j -
        abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j) ^ 2)
      ≤ᵐ[M.P.toMeasure]
    fun omega : Sample d =>
      2 * ∑ u : Fin d, ∑ v : Fin d,
        (descendantsAverage (originCube d (n : ℤ)) (n - L)
          (fun R =>
            (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ u v -
              abarStarInv M L
                (Ch02.cubeDomain (originCube d (n : ℤ))) u v)) ^ 2 +
      8 * (descendantsAverage (originCube d (n : ℤ)) (n - L)
        (fun R => ∑ u : Fin d, cutoffResponseOnCube M L
          ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R omega)) ^ 2 := by
  let k := aCutoffNormalizationDepth d L
  let center : ℤ := (n : ℤ) - (k : ℤ)
  let Q : TriadicCube d := originCube d center
  let S := combineInvSqrtNormalizer (d := d) (ahom M L)
  let T := combineSqrtNormalizer (d := d) (ahom M L)
  have htwo := fullBlock_two_plus_eight_rescaled_aCutoff_ae
    M L center S T Q (n - L)
  filter_upwards [htwo] with omega homega
  have hparent := sq_ahom_mul_centered_randomAStarInv_entry_le_fullBlockFluctuation
    M L omega (n : ℤ) i j
  have hdesc :=
    descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_literalDualAverage
      M L omega (n : ℤ) Q (n - L)
  have htrace := blockJTraceAverageSqWithNormalizers_normalized_eq
    M L omega Q (n - L)
  have hdilate : Ch02.dilateCube (k : ℤ) Q = originCube d (n : ℤ) := by
    simpa [Q, center, k] using! dilateCube_originCube_sub d (n : ℤ) (k : ℤ)
  dsimp only [S, T] at homega
  rw [htrace, hdilate] at homega
  rw [hdilate] at hdesc
  have halpha : 0 < ahom M L := ahom_pos M L
  have hscaled :
      (ahom M L) ^ 2 *
        ((randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j -
          abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j) ^ 2 ≤
        (ahom M L) ^ 2 *
          (2 * ∑ u : Fin d, ∑ v : Fin d,
              (descendantsAverage (originCube d (n : ℤ)) (n - L)
                (fun R =>
                  (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ u v -
                    abarStarInv M L
                      (Ch02.cubeDomain (originCube d (n : ℤ))) u v)) ^ 2 +
            8 * (descendantsAverage (originCube d (n : ℤ)) (n - L)
              (fun R => ∑ u : Fin d, cutoffResponseOnCube M L
                ((ahom M L)⁻¹ • Pi.single u 1)
                (Pi.single u 1) R omega)) ^ 2) := by
    calc
      _ ≤ Ch05.Section56.fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
          ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized k)
          (aCutoffNormalization_structuralLaw M L) center
          (combineInvSqrtNormalizer (ahom M L)) Q
          (rescaleReg k (aCutoffRegCoeffField M L omega)) := by
            simpa only [Q, center, k, mul_pow] using! hparent
      _ ≤ 2 *
            Ch05.Section56.descendantsAverageFluctuationOperatorNormSqWithNormalizer
              ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized k)
              (aCutoffNormalization_structuralLaw M L) center
              (combineInvSqrtNormalizer (ahom M L)) Q (n - L)
              (rescaleReg k (aCutoffRegCoeffField M L omega)) +
          8 * ((ahom M L) ^ 2 *
            (descendantsAverage (originCube d (n : ℤ)) (n - L)
              (fun R => ∑ u : Fin d, cutoffResponseOnCube M L
                ((ahom M L)⁻¹ • Pi.single u 1)
                (Pi.single u 1) R omega)) ^ 2) := homega
      _ ≤ _ := by
        have hdesc' := mul_le_mul_of_nonneg_left hdesc (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
  have hscaled' := hscaled
  ring_nf at hscaled'
  nlinarith [sq_pos_of_pos halpha]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
