module

public import SubdiffusiveProcess.CoarseGrainingVocab.PaperFractionalDualBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.SharpCompareJ
public import Homogenization.Book.Ch03.ABK26.FluxComparisonCZ
public import Homogenization.Book.Ch03.ABK26.LocalCoarseGraining
public import Homogenization.Book.Ch02.Theorems.Quadraticity
public import Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorControl
public import Homogenization.Sobolev.Fractional.ExactOverlapEuclideanLpComparison
public import Homogenization.Sobolev.Fractional.EuclideanWspSmoothDualBesovBound

@[expose] public section




namespace SubdiffusiveProcess.Providers.Section2

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal MatrixOrder

noncomputable section

/- Adapted from the private
`ABK26.memVectorL2_matVecMul_pointwiseCoeffOn`; the library declaration cannot
be imported outside its source file. -/
private theorem memVectorL2_matVecMul_coeffOn {d : ℕ}
    {Q : Homogenization.TriadicCube d}
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul (a.toCoeffField x) (u.grad x)) := by
  let b : Ch02.CoeffOn (Ch02.cubeDomain Q) :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn (Ch02.cubeDomain Q) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet Q) b.toCoeffField := by
    simpa only [b, Ch02.cubeDomain_coe] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
        (Ch02.cubeDomain Q) a
  have hB : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul (b.toCoeffField x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] a.toCoeffField := by
    simpa only [b, Ch02.cubeDomain_coe] using!
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq
        (Ch02.cubeDomain Q) a
  apply (memLp_congr_ae ?_).mp hB
  filter_upwards [hba] with x hx
  simp only [hx]


private theorem vecDot_sub_left {d : ℕ}
    (x y z : Homogenization.Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/- Adapted from the private
`ABK26.centeredCube_normalizedVolume_eq_smul_openCubeVolume`; the library
declaration cannot be imported outside its source file. -/
private theorem centeredCube_normalizedVolume_eq {d : ℕ} {m : ℤ} :
    (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- Two forced equations with the same forcing give the flux-balance input of
the fractional CZ comparison. -/
theorem isCenteredCubeFluxBalanced_of_forced {d : ℕ} {m : ℤ}
    (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    {sigma0 : ℝ} {u v : H1Function (openCubeSet (originCube d m))}
    {g : Homogenization.Vec d → Homogenization.Vec d}
    (hu : IsForcedEquation (originCube d m) a u g)
    (hv : IsScalarForcedEquation (originCube d m) sigma0 v g) :
    IsCenteredCubeFluxBalanced m a sigma0 u v := by
  intro phi
  have hI1 : IntegrableOn (fun x =>
      vecDot (matVecMul (a.toCoeffField x) (u.grad x))
        (phi.toH1Function.grad x)) (openCubeSet (originCube d m)) :=
    integrableOn_vecDot_of_memVectorL2 (memVectorL2_matVecMul_coeffOn a u)
      phi.toH1Function.grad_memVectorL2
  have hI2 : IntegrableOn (fun x =>
      vecDot (sigma0 • v.grad x) (phi.toH1Function.grad x))
      (openCubeSet (originCube d m)) :=
    integrableOn_vecDot_of_memVectorL2 (v.grad_memVectorL2.const_smul sigma0)
      phi.toH1Function.grad_memVectorL2
  have hzero : ∫ x in openCubeSet (originCube d m),
      vecDot (matVecMul (a.toCoeffField x) (u.grad x) - sigma0 • v.grad x)
        (phi.toH1Function.grad x) ∂volume = 0 := by
    have hpt : (fun x => vecDot
        (matVecMul (a.toCoeffField x) (u.grad x) - sigma0 • v.grad x)
        (phi.toH1Function.grad x)) =
        fun x => vecDot (matVecMul (a.toCoeffField x) (u.grad x))
            (phi.toH1Function.grad x) -
          vecDot (sigma0 • v.grad x) (phi.toH1Function.grad x) := by
      funext x
      exact vecDot_sub_left _ _ _
    have hv' := hv phi
    simp only [matVecMul_scalarMatrix] at hv'
    rw [hpt, MeasureTheory.integral_sub hI1 hI2, hu phi, hv']
    ring
  rw [centeredCube_normalizedVolume_eq, MeasureTheory.integral_smul_measure,
    smul_eq_mul, hzero, mul_zero]


private theorem centeredCubeLocalFluxDefectL2Field_eq {d : ℕ}
    {m n : ℤ} (hnm : n < m) (hn : n ≤ (originCube d m).scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ)
    (u : H1Function (openCubeSet (originCube d m)))
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ descendantsAtScale (originCube d m) n) :
    centeredCubeLocalFluxDefectL2Field m n hnm a sigma0 u R hR =
      localFluxDefectL2Field a
        (openCubeSet_subset_of_mem_descendantsAtScale hn hR) sigma0 u := rfl


private theorem finiteLpExponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne

private theorem coeffOn_transpose_aeeq_self_of_symmetric {d : ℕ}
    {U : Ch02.Domain d} {a : Ch02.CoeffOn U} (ha : a.IsSymmetric) :
    Ch02.CoeffOn.AEEq a.transpose a := by
  filter_upwards [ha] with x hx
  exact hx

private theorem vecNormSq_add_add_sub {d : ℕ}
    (x y : Homogenization.Vec d) :
    vecNormSq (x - y) + vecNormSq (x + y) =
      2 * (vecNormSq x + vecNormSq y) := by
  unfold vecNormSq vecDot
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ i, ((x i - y i) * (x i - y i) + (x i + y i) * (x i + y i)) =
        ∑ i, 2 * (x i * x i + y i * y i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 2 * ∑ i, (x i * x i + y i * y i) := by rw [Finset.mul_sum]
    _ = 2 * ((∑ i, x i * x i) + ∑ i, y i * y i) := by
          rw [Finset.sum_add_distrib]

private theorem diagonal_mulVec_apply {n : Type*} [Fintype n] [DecidableEq n]
    (f x : n → ℝ) (i : n) :
    Matrix.mulVec (Matrix.diagonal f) x i = f i * x i := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Matrix.diagonal]
    simp [Ne.symm hji]
  · simp

/-- Under symmetry, the full normalized block response is bounded by the
paper's scalar normalized probe.  The doubled scalar splitting evaluates the
two linked probes in the directions `x-y` and `x+y`; the parallelogram identity
then spends exactly the full-block unit norm. -/
theorem normalizedBlockResponseMax_le_paperScalarProbeMax {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (ha : (a.coeffOn Q).IsSymmetric) {alpha : ℝ} (halpha : 0 < alpha) :
    ENNReal.ofReal (Ch02.normalizedBlockResponseMax Q a
      (scalarMatrix (d := d) alpha)) ≤ paperScalarProbeMax Q a alpha := by
  classical
  let U := Ch02.cubeDomain Q
  let aQ := a.coeffOn Q
  let b : Homogenization.Mat d := scalarMatrix (d := d) alpha
  let R : Homogenization.Mat d := sharpResponseMatrix U aQ b
  have hb : b.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · change (scalarMatrix (d := d) alpha).IsSymm
      exact scalarMatrix_isSymm alpha
    · intro x hx
      have hxpos : 0 < vecNormSq x :=
        lt_of_le_of_ne (vecNormSq_nonneg x) (by
          simpa [vecNormSq_eq_zero_iff, eq_comm] using hx)
      have := mul_pos halpha hxpos
      change 0 < vecDot x (matVecMul b x)
      rw [show matVecMul b x = alpha • x by
        simpa [b] using matVecMul_scalarMatrix alpha x]
      simpa [vecDot_smul_right, vecNormSq] using! this
  have hsqrtSmall : matrixSqrt b = Real.sqrt alpha • (1 : Homogenization.Mat d) := by
    dsimp [matrixSqrt]
    apply CFC.sqrt_unique
    · calc
        (Real.sqrt alpha • (1 : Homogenization.Mat d)) *
              (Real.sqrt alpha • (1 : Homogenization.Mat d)) =
            (Real.sqrt alpha * Real.sqrt alpha) •
              ((1 : Homogenization.Mat d) * 1) := by
                rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = alpha • (1 : Homogenization.Mat d) := by
              rw [one_mul, Real.mul_self_sqrt halpha.le]
        _ = b := rfl
    · rw [Matrix.nonneg_iff_posSemidef]
      exact Matrix.PosSemidef.one.smul (Real.sqrt_nonneg alpha)
  have hinvsqrtSmall : matrixInvSqrt b =
      (Real.sqrt alpha)⁻¹ • (1 : Homogenization.Mat d) := by
    unfold matrixInvSqrt
    rw [show CFC.sqrt b = Real.sqrt alpha • (1 : Homogenization.Mat d) from hsqrtSmall]
    rw [nonsing_inv_smul (Real.sqrt alpha) (Real.sqrt_ne_zero'.mpr halpha) (by simp)]
    simp
  have hR : R.PosSemidef := sharpResponseMatrix_posSemidef U aQ ha b
  have hquad : ∀ z : Homogenization.Vec d,
      J U aQ ((Real.sqrt alpha)⁻¹ • z) (Real.sqrt alpha • z) =
        vecDot z (matVecMul R z) := by
    intro z
    rw [← sharpResponse_quadratic U aQ ha b hb z]
    rw [hsqrtSmall, hinvsqrtSmall]
    rw [smul_matVecMul, smul_matVecMul]
    rw [show matVecMul (1 : Homogenization.Mat d) z = z from Matrix.one_mulVec z]
  have hpaperOn : paperScalarProbeMaxOn U aQ alpha =
      ENNReal.ofReal (Ch02.matrixOperatorNorm R) :=
    paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm U aQ alpha R hR hquad
  have htranspose : Ch02.CoeffOn.AEEq aQ.transpose aQ :=
    coeffOn_transpose_aeeq_self_of_symmetric ha
  have hbound (z : Homogenization.Vec d) :
      J U aQ ((Real.sqrt alpha)⁻¹ • z) (Real.sqrt alpha • z) ≤
        Ch02.matrixOperatorNorm R * vecNormSq z := by
    rw [hquad]
    exact Ch02.vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef hR z
  have hsqrt :=
    Homogenization.Book.Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
      (d := d) halpha
  have hinvsqrt :=
    Homogenization.Book.Ch05.Section57.constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt
      (d := d) halpha
  have hmax : Ch02.normalizedBlockResponseMax Q a b ≤ Ch02.matrixOperatorNorm R := by
    unfold Ch02.normalizedBlockResponseMax
    refine csSup_le (Ch02.normalizedBlockResponseValueSet_nonempty Q a b) ?_
    rintro value ⟨e, he, rfl⟩
    let x : Homogenization.Vec d := fun i => e (Sum.inl i)
    let y : Homogenization.Vec d := fun i => e (Sum.inr i)
    let P : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt b) e)
    let T : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt b) e)
    have hP : P = ((Real.sqrt alpha)⁻¹ • x, Real.sqrt alpha • y) := by
      dsimp only [P]
      rw [show b = scalarMatrix (d := d) alpha by rfl, hinvsqrt]
      ext i
      · change Matrix.mulVec
            (Matrix.diagonal
              (Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag alpha alpha))
            e (Sum.inl i) = _
        rw [diagonal_mulVec_apply]
        simp [Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag, x]
      · change Matrix.mulVec
            (Matrix.diagonal
              (Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag alpha alpha))
            e (Sum.inr i) = _
        rw [diagonal_mulVec_apply]
        simp [Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag, y]
    have hT : T = (Real.sqrt alpha • x, (Real.sqrt alpha)⁻¹ • y) := by
      dsimp only [T]
      rw [show b = scalarMatrix (d := d) alpha by rfl, hsqrt]
      ext i
      · change Matrix.mulVec
            (Matrix.diagonal
              (Homogenization.Book.Ch05.Section56.scalarFullBlockSqrtDiag alpha alpha))
            e (Sum.inl i) = _
        rw [diagonal_mulVec_apply]
        simp [Homogenization.Book.Ch05.Section56.scalarFullBlockSqrtDiag, x]
      · change Matrix.mulVec
            (Matrix.diagonal
              (Homogenization.Book.Ch05.Section56.scalarFullBlockSqrtDiag alpha alpha))
            e (Sum.inr i) = _
        rw [diagonal_mulVec_apply]
        simp [Homogenization.Book.Ch05.Section56.scalarFullBlockSqrtDiag, y]
    rw [show ofFullBlockVec
        (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt b) e) = P by rfl,
      show ofFullBlockVec
        (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt b) e) = T by rfl,
      hP, hT]
    rw [Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum]
    rw [Ch02.responseJ_eq_ofAEEq htranspose]
    have hminus :
        (Real.sqrt alpha)⁻¹ • x - (Real.sqrt alpha)⁻¹ • y =
          (Real.sqrt alpha)⁻¹ • (x - y) := by module
    have hplus :
        (Real.sqrt alpha)⁻¹ • y + (Real.sqrt alpha)⁻¹ • x =
          (Real.sqrt alpha)⁻¹ • (x + y) := by
      module
    have hminusQ :
        Real.sqrt alpha • x - Real.sqrt alpha • y =
          Real.sqrt alpha • (x - y) := by module
    have hplusQ :
        Real.sqrt alpha • x + Real.sqrt alpha • y =
          Real.sqrt alpha • (x + y) := by
      module
    rw [hminus, hminusQ, hplus, hplusQ]
    have hxy : vecNormSq x + vecNormSq y = 1 := by
      simpa [Ch02.fullBlockVecNormSq, vecNormSq, vecDot, x, y,
        Fintype.sum_sum_type, pow_two] using he
    have hM0 : 0 ≤ Ch02.matrixOperatorNorm R :=
      Ch02.matrixOperatorNorm_nonneg R
    calc
      (1 / 2 : ℝ) * J U aQ ((Real.sqrt alpha)⁻¹ • (x - y))
            (Real.sqrt alpha • (x - y)) +
          (1 / 2 : ℝ) * J U aQ ((Real.sqrt alpha)⁻¹ • (x + y))
            (Real.sqrt alpha • (x + y)) ≤
          (1 / 2 : ℝ) *
              (Ch02.matrixOperatorNorm R * vecNormSq (x - y)) +
            (1 / 2 : ℝ) *
              (Ch02.matrixOperatorNorm R * vecNormSq (x + y)) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left (hbound (x - y)) (by norm_num))
                  (mul_le_mul_of_nonneg_left (hbound (x + y)) (by norm_num))
      _ = Ch02.matrixOperatorNorm R := by
            have hpara := vecNormSq_add_add_sub x y
            nlinarith
  calc
    ENNReal.ofReal (Ch02.normalizedBlockResponseMax Q a
        (scalarMatrix (d := d) alpha)) ≤
        ENNReal.ofReal (Ch02.matrixOperatorNorm R) := ENNReal.ofReal_le_ofReal hmax
    _ = paperScalarProbeMaxOn U aQ alpha := hpaperOn.symm
    _ = paperScalarProbeMax Q a alpha := rfl

private theorem paperScalarProbeMax_eq_of_localAEEq {d : ℕ}
    {A B : Ch02.TriadicCoeffFamily d} {Q : Homogenization.TriadicCube d}
    (h : Ch02.CoeffOn.AEEq (A.coeffOn Q) (B.coeffOn Q)) (alpha : ℝ) :
    paperScalarProbeMax Q A alpha = paperScalarProbeMax Q B alpha := by
  unfold paperScalarProbeMax paperScalarProbe
  apply iSup_congr
  intro e
  congr 1
  exact Ch02.responseJ_eq_ofAEEq h _ _

private theorem coeffOn_isSymmetric_of_aeeq {d : ℕ} {U : Ch02.Domain d}
    {a b : Ch02.CoeffOn U} (h : Ch02.CoeffOn.AEEq a b)
    (hb : b.IsSymmetric) :
    a.IsSymmetric := by
  filter_upwards [h, hb] with x hx hsymm
  simpa only [hx] using hsymm

/-- The parent-truncated one-scale response used by the local theorem is
bounded by the paper's scalar descendant maximum.  Compatibility of the
triadic family is used only modulo a.e. equality on each descendant. -/
theorem parentTruncatedResponseAtScale_le_paperMaxDescendant {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (ha : ∀ R, (a.coeffOn R).IsSymmetric)
    (alpha : ℝ) (halpha : 0 < alpha) :
    Ch02.parentTruncatedNormalizedBlockResponseScalarEMaxAtScale Q k hk
        (a.coeffOn Q) alpha halpha ≤
      paperMaxDescendantProbeAtScale Q k a alpha := by
  classical
  let A := rootPointwiseCoeffFamily Q (a.coeffOn Q)
  unfold Ch02.parentTruncatedNormalizedBlockResponseScalarEMaxAtScale
  change (descendantsAtScale Q k).attach.sup (fun R =>
      Ch02.normalizedBlockResponseScalarEMaxOnCube R.1
        ((a.coeffOn Q).restrictToSubcube
          (openCubeSet_subset_of_mem_descendantsAtScale hk R.2)) alpha halpha) ≤ _
  apply Finset.sup_le
  intro R _hR
  have hroot := rootPointwiseCoeffFamily_descendant_aeeq
    Q (a.coeffOn Q) hk R.2
  have hrestrict : Ch02.CoeffOn.AEEq
      ((a.coeffOn Q).restrictToSubcube
        (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))
      (a.coeffOn R.1) := by
    simpa only [Ch02.CoeffOn.restrictToSubcube_toCoeffField] using!
      (a.restrictsTo_descendant hk R.2).symm
  have hrootOriginal : Ch02.CoeffOn.AEEq (A.coeffOn R.1) (a.coeffOn R.1) :=
    hroot.trans hrestrict
  rw [normalizedBlockResponseScalarEMaxOnCube_eq_ofReal_rootPointwise
    Q (a.coeffOn Q) alpha halpha hk R.2]
  calc
    ENNReal.ofReal (Ch02.normalizedBlockResponseMax R.1 A
        (scalarMatrix (d := d) alpha)) ≤
        paperScalarProbeMax R.1 A alpha :=
      normalizedBlockResponseMax_le_paperScalarProbeMax R.1 A
        (coeffOn_isSymmetric_of_aeeq hrootOriginal (ha R.1)) halpha
    _ = paperScalarProbeMax R.1 a alpha :=
      paperScalarProbeMax_eq_of_localAEEq hrootOriginal alpha
    _ ≤ paperMaxDescendantProbeAtScale Q k a alpha := by
      exact le_iSup (fun S : {S : Homogenization.TriadicCube d //
        S ∈ descendantsAtScale Q k} => paperScalarProbeMax S.1 a alpha) R

theorem parentTruncatedErrorOne_le_paperHomogenizationError {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (ha : ∀ R, (a.coeffOn R).IsSymmetric)
    (alpha : ℝ) (halpha : 0 < alpha) (s : FractionalOrder) :
    Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn
        (a.coeffOn Q) alpha halpha s ≤
      paperHomogenizationError Q n s.1 .infinity (.finite 1) a alpha := by
  rw [Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar_eq_tsum]
  unfold paperHomogenizationError paperHomogenizationErrorFinite
  simp only [paperScaleResponseAtScale, Ch02.geometricWeight,
    Ch02.geometricDiscount, mul_one, neg_mul, one_div, ENNReal.rpow_one]
  norm_num
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [ENNReal.ofReal_mul (by
    exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [s.2.1])))]
  gcongr
  exact parentTruncatedResponseAtScale_le_paperMaxDescendant Q
    (n - (j : ℤ)) (by omega) a ha alpha halpha

theorem parentTruncatedErrorTwo_le_paperHomogenizationError {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (ha : ∀ R, (a.coeffOn R).IsSymmetric)
    (alpha : ℝ) (halpha : 0 < alpha) (s : FractionalOrder) :
    Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn
        (a.coeffOn Q) alpha halpha s ≤
      paperHomogenizationError Q n s.1 .infinity (.finite 2) a alpha := by
  rw [Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_tsum]
  unfold paperHomogenizationError paperHomogenizationErrorFinite
  simp only [paperScaleResponseAtScale, Ch02.geometricWeight,
    Ch02.geometricDiscount, one_div]
  norm_num
  gcongr with j
  rw [ENNReal.ofReal_mul (by
    exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by nlinarith [s.2.1])))]
  calc
    Ch02.parentTruncatedNormalizedBlockResponseScalarEMaxAtScale Q
        (n - (j : ℤ)) (by omega) (a.coeffOn Q) alpha halpha ≤
        paperMaxDescendantProbeAtScale Q (n - (j : ℤ)) a alpha :=
      parentTruncatedResponseAtScale_le_paperMaxDescendant Q
        (n - (j : ℤ)) (by omega) a ha alpha halpha
    _ = (paperMaxDescendantProbeAtScale Q (n - (j : ℤ)) a alpha ^
          (1 / 2 : ℝ)) ^ (2 : ℕ) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

/-- The p-general descendant aggregation linking the CZ output to the local
negative-Besov input. -/
theorem localFluxDefect_smoothDualAverage_le {d : ℕ} [NeZero d]
    {m n : ℤ} (hnm : n < m) (hn : n ≤ (originCube d m).scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ)
    (u : H1Function (openCubeSet (originCube d m)))
    (s : FractionalOrder) (p : FiniteLpExponent) :
    centeredCubeLocalFluxDefectSmoothDualLpAverage m n hnm a sigma0 u s p ≤
      cubeEuclideanNegativeWspSmoothDualBesovConstant d *
          ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) *
        localFluxDefectNegativeBesovLpAverage (originCube d m) n hn
          a sigma0 u s p := by
  classical
  let t : ℝ := p.exponent.toReal
  have ht : 0 < t := finiteLpExponent_toReal_pos p
  let Cd : ℝ≥0∞ := cubeEuclideanNegativeWspSmoothDualBesovConstant d
  let D := descendantsAtScale (originCube d m) n
  let g : {x // x ∈ D} → ℝ≥0∞ := fun R =>
    cubeEuclideanNegativeBesovESeminorm R.1 s p
      (localFluxDefectL2Field a
        (openCubeSet_subset_of_mem_descendantsAtScale hn R.2) sigma0 u)
  let f : {x // x ∈ D} → ℝ≥0∞ := fun R =>
    cubeEuclideanNegativeWspSmoothDualENorm R.1 s p
      (centeredCubeLocalFluxDefectL2Field m n hnm a sigma0 u R.1 R.2)
  have hpt : ∀ R : {x // x ∈ D}, f R ≤ Cd * g R := by
    intro R
    have h :=
      cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm
        d R.1 s p (localFluxDefectL2Field a
          (openCubeSet_subset_of_mem_descendantsAtScale hn R.2) sigma0 u)
    simpa only [f, g, Cd,
      centeredCubeLocalFluxDefectL2Field_eq hnm hn a sigma0 u R.1 R.2] using h
  have hsum : (∑ R ∈ D.attach, f R ^ t) ≤
      Cd ^ t * ∑ R ∈ D.attach, g R ^ t := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun R _ => ?_
    calc
      f R ^ t ≤ (Cd * g R) ^ t := ENNReal.rpow_le_rpow (hpt R) ht.le
      _ = Cd ^ t * g R ^ t := ENNReal.mul_rpow_of_nonneg _ _ ht.le
  have havg : ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, f R ^ t) ≤
      Cd ^ t * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) := by
    calc
      ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, f R ^ t) ≤
          (D.card : ℝ≥0∞)⁻¹ * (Cd ^ t * ∑ R ∈ D.attach, g R ^ t) := by
            gcongr
      _ = Cd ^ t * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) := by
            ring
  have hroot : ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, f R ^ t) ^ t⁻¹ ≤
      Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ := by
    calc
      ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, f R ^ t) ^ t⁻¹ ≤
          (Cd ^ t * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t)) ^ t⁻¹ :=
            ENNReal.rpow_le_rpow havg (inv_nonneg.mpr ht.le)
      _ = (Cd ^ t) ^ t⁻¹ *
          ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ :=
            ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr ht.le)
      _ = Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ := by
            rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]
  have hnorm : ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) *
      ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ))) = 1 := by
    have hnonneg : 0 ≤ Real.rpow 3 (s.1 * (n : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hprod : Real.rpow 3 (s.1 * (n : ℝ)) *
        Real.rpow 3 (-s.1 * (n : ℝ)) = 1 := by
      show (3 : ℝ) ^ (s.1 * (n : ℝ)) * (3 : ℝ) ^ (-s.1 * (n : ℝ)) = 1
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      have hadd : s.1 * (n : ℝ) + -s.1 * (n : ℝ) = 0 := by ring
      rw [hadd, Real.rpow_zero]
    rw [← ENNReal.ofReal_mul hnonneg]
    rw [hprod, ENNReal.ofReal_one]
  rw [centeredCubeLocalFluxDefectSmoothDualLpAverage,
    localFluxDefectNegativeBesovLpAverage, one_div]
  calc
    ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, f R ^ t) ^ t⁻¹ ≤
        Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ := hroot
    _ = Cd * ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) *
        (ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ))) *
          ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹) := by
          calc
            Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹ =
                (ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) *
                    ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ)))) *
                  (Cd * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach, g R ^ t) ^ t⁻¹) := by
                    rw [hnorm, one_mul]
            _ = _ := by ring


theorem aux_dedup_d071_localCoarseGrainingLpRHS_const_mul {d : ℕ} [NeZero d]
    (K C : ℝ≥0∞) (Q : Homogenization.TriadicCube d)
    (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (hsigma0 : 0 < sigma0)
    (g : Homogenization.Vec d → Homogenization.Vec d)
    (u : H1Function (openCubeSet Q)) (s1 s s2 : FractionalOrder)
    (p : FiniteLpExponent) :
    K * localCoarseGrainingLpRHS C Q n hn a sigma0 hsigma0 g u s1 s s2 p =
      localCoarseGrainingLpRHS (K * C) Q n hn a sigma0 hsigma0 g u s1 s s2 p := by
  unfold localCoarseGrainingLpRHS
  ring

private theorem localCoarseGrainingLpRHS_const_mul {d : ℕ} [NeZero d]
    (K C : ℝ≥0∞) (Q : Homogenization.TriadicCube d)
    (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (hsigma0 : 0 < sigma0)
    (g : Homogenization.Vec d → Homogenization.Vec d)
    (u : H1Function (openCubeSet Q)) (s1 s s2 : FractionalOrder)
    (p : FiniteLpExponent) :
    K * localCoarseGrainingLpRHS C Q n hn a sigma0 hsigma0 g u s1 s s2 p =
      localCoarseGrainingLpRHS (K * C) Q n hn a sigma0 hsigma0 g u s1 s s2 p := by exact SubdiffusiveProcess.Providers.Section2.aux_dedup_d071_localCoarseGrainingLpRHS_const_mul (d := d) (K := K) (C := C) (Q := Q) (n := n) (hn := hn) (a := a) (sigma0 := sigma0) (hsigma0 := hsigma0) (g := g) (u := u) (s1 := s1) (s := s) (s2 := s2) (p := p)

/-- The ABK26 exact-overlap carrier is unnormalized in `s`.  Appendix C gives
the dimension-uniform comparison to the equally unnormalized Gagliardo
carrier; translating the latter to the manuscript's normalized seminorm costs
exactly `s ^ (-1 / p)`.
 -/
theorem cubeEuclideanPositiveBesovOverlapESeminorm_le_paperFractionalSeminorm
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q p) :
    Homogenization.cubeEuclideanPositiveBesovOverlapESeminorm Q s p F ≤
      cubeEuclideanWspOverlapDimensionConstant d *
        (ENNReal.ofReal s.1) ^ (-(p.exponent.toReal)⁻¹) *
          paperFractionalSeminorm Q s p F := by
  let b : ℝ≥0∞ := ENNReal.ofReal s.1
  let r : ℝ := (p.exponent.toReal)⁻¹
  have hb0 : b ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr s.2.1
  have hbtop : b ≠ ∞ := ENNReal.ofReal_ne_top
  have hcancel : b ^ (-r) * (b ^ r) = 1 := by
    rw [← ENNReal.rpow_add _ _ hb0 hbtop]
    simp
  calc
    Homogenization.cubeEuclideanPositiveBesovOverlapESeminorm Q s p F ≤
        cubeEuclideanWspOverlapDimensionConstant d *
          cubeEuclideanWspESeminorm Q s p F :=
      cubeEuclideanOverlap_le_dimensionConstant_mul_wsp Q s p F
    _ = cubeEuclideanWspOverlapDimensionConstant d * b ^ (-r) *
          (b ^ r * cubeEuclideanWspESeminorm Q s p F) := by
      calc
        cubeEuclideanWspOverlapDimensionConstant d *
            cubeEuclideanWspESeminorm Q s p F =
          cubeEuclideanWspOverlapDimensionConstant d * 1 *
            cubeEuclideanWspESeminorm Q s p F := by rw [mul_one]
        _ = _ := by rw [← hcancel]; ring
    _ = _ := by rfl


theorem aux_dedup_d158_ofReal_three_rpow_scale_triple (s : ℝ) (m n : ℤ) :
    ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
        ENNReal.ofReal (Real.rpow 3 (s * (((m - n : ℤ) : ℝ)))) *
      ENNReal.ofReal (Real.rpow 3 (s * (n : ℝ))) = 1 := by
  have hnonneg : ∀ x : ℝ, 0 ≤ Real.rpow 3 x := fun x => Real.rpow_nonneg (by norm_num) x
  rw [← ENNReal.ofReal_mul (hnonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (hnonneg _) (hnonneg _))]
  have hreal : Real.rpow 3 (-s * (m : ℝ)) *
      Real.rpow 3 (s * (((m - n : ℤ) : ℝ))) *
      Real.rpow 3 (s * (n : ℝ)) = 1 := by
    show (3 : ℝ) ^ (-s * (m : ℝ)) *
        (3 : ℝ) ^ (s * (((m - n : ℤ) : ℝ))) *
        (3 : ℝ) ^ (s * (n : ℝ)) = 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hexp : -s * (m : ℝ) + s * (((m - n : ℤ) : ℝ)) +
        s * (n : ℝ) = 0 := by
      push_cast
      ring
    rw [hexp, Real.rpow_zero]
  rw [hreal, ENNReal.ofReal_one]

private theorem ofReal_three_rpow_scale_triple (s : ℝ) (m n : ℤ) :
    ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
        ENNReal.ofReal (Real.rpow 3 (s * (((m - n : ℤ) : ℝ)))) *
      ENNReal.ofReal (Real.rpow 3 (s * (n : ℝ))) = 1 := by exact SubdiffusiveProcess.Providers.Section2.aux_dedup_d158_ofReal_three_rpow_scale_triple (s := s) (m := m) (n := n)

/-- The complete finite-`p` library assembly, before translating its local RHS
to the paper's response, energy, and forcing carriers. -/
theorem exists_generalCoarseGraining_paperDual_libraryRHS
    (d : ℕ) (hd : 2 ≤ d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m n : ℤ) (hnm : n < m) (s1 s s2 : FractionalOrder),
        s1.1 < s.1 → s.1 < s2.1 →
      ∀ (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
        (g : Homogenization.Vec d → Homogenization.Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma0 v g →
        HasH10Difference (originCube d m) u v →
        ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
            (ENNReal.ofReal sigma0 * paperNegativeFractionalDual
                (originCube d m) s p (centeredCubeGradientDifferenceL2Field m u v) +
              paperNegativeFractionalDual (originCube d m) s p
                (centeredCubeFluxDifferenceL2Field m a sigma0 u v)) ≤
          (ENNReal.ofReal s.1) ^ (-(p.conjugate.exponent.toReal)⁻¹) *
            localCoarseGrainingLpRHS C (originCube d m) n
              (by simpa [originCube] using hnm.le) a sigma0 hsigma0
              g u s1 s s2 p := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Ccz, hCczTop, hCcz⟩ := exists_centeredCubeFluxComparison_cz d hd p hp
  obtain ⟨Clc, hClcTop, hClc⟩ := exists_localCoarseGrainingLp d hd
  let Cd := cubeEuclideanNegativeWspSmoothDualBesovConstant d
  refine ⟨Ccz * Cd * Clc, ?_, ?_⟩
  · exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hCczTop
        (cubeEuclideanNegativeWspSmoothDualBesovConstant_lt_top d)) hClcTop
  intro m n hnm s1 s s2 hs1s hss2 a sigma0 hsigma0 g hg u v hu hv hzero
  have hn : n ≤ (originCube d m).scale := by simpa [originCube] using hnm.le
  have hbal := isCenteredCubeFluxBalanced_of_forced a hu hv
  have hcz := hCcz m n hnm a sigma0 hsigma0 s u v hbal hzero
  have hmiddle := localFluxDefect_smoothDualAverage_le hnm hn a sigma0 u s p
  have hlocal := hClc p hp m n hnm s1 s s2 hs1s hss2
    a sigma0 hsigma0 g hg u hu
  let K : ℝ≥0∞ := (ENNReal.ofReal s.1) ^ (-(p.conjugate.exponent.toReal)⁻¹)
  have hgrad := paperNegativeFractionalDual_le_smoothDual
    (originCube d m) s p (centeredCubeGradientDifferenceL2Field m u v)
  have hflux := paperNegativeFractionalDual_le_smoothDual
    (originCube d m) s p (centeredCubeFluxDifferenceL2Field m a sigma0 u v)
  have hlhs : ENNReal.ofReal sigma0 * paperNegativeFractionalDual
        (originCube d m) s p (centeredCubeGradientDifferenceL2Field m u v) +
      paperNegativeFractionalDual (originCube d m) s p
        (centeredCubeFluxDifferenceL2Field m a sigma0 u v) ≤
      K * centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p := by
    unfold centeredCubeFluxComparisonSmoothDualLHS
    dsimp only [K]
    calc
      _ ≤ ENNReal.ofReal sigma0 *
            (K * cubeEuclideanNegativeWspSmoothDualENorm
              (originCube d m) s p (centeredCubeGradientDifferenceL2Field m u v)) +
          K * cubeEuclideanNegativeWspSmoothDualENorm
            (originCube d m) s p
              (centeredCubeFluxDifferenceL2Field m a sigma0 u v) :=
        add_le_add (mul_le_mul_right hgrad _) hflux
      _ = K * (ENNReal.ofReal sigma0 *
            cubeEuclideanNegativeWspSmoothDualENorm
              (originCube d m) s p (centeredCubeGradientDifferenceL2Field m u v) +
          cubeEuclideanNegativeWspSmoothDualENorm
            (originCube d m) s p
              (centeredCubeFluxDifferenceL2Field m a sigma0 u v)) := by ring
  let W : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ)))
  let Wmn : ℝ≥0∞ := ENNReal.ofReal
    (Real.rpow 3 (s.1 * (((m - n : ℤ) : ℝ))))
  let Wn : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ)))
  have htriple : W * Wmn * Wn = 1 := ofReal_three_rpow_scale_triple s.1 m n
  calc
    W * (ENNReal.ofReal sigma0 * paperNegativeFractionalDual
          (originCube d m) s p (centeredCubeGradientDifferenceL2Field m u v) +
        paperNegativeFractionalDual (originCube d m) s p
          (centeredCubeFluxDifferenceL2Field m a sigma0 u v)) ≤
        W * (K * centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p) := by
          gcongr
    _ ≤ W * (K * (Ccz * Wmn *
          centeredCubeLocalFluxDefectSmoothDualLpAverage
            m n hnm a sigma0 u s p)) := by gcongr
    _ ≤ W * (K * (Ccz * Wmn * (Cd * Wn *
          localFluxDefectNegativeBesovLpAverage
            (originCube d m) n hn a sigma0 u s p))) := by gcongr
    _ = K * (Ccz * Cd *
          localFluxDefectNegativeBesovLpAverage
            (originCube d m) n hn a sigma0 u s p) := by
          calc
            W * (K * (Ccz * Wmn * (Cd * Wn *
                localFluxDefectNegativeBesovLpAverage
                  (originCube d m) n hn a sigma0 u s p))) =
                (W * Wmn * Wn) *
                  (K * Ccz * Cd * localFluxDefectNegativeBesovLpAverage
                    (originCube d m) n hn a sigma0 u s p) := by ring
            _ = _ := by rw [htriple, one_mul]; ring
    _ ≤ K * (Ccz * Cd *
          localCoarseGrainingLpRHS Clc (originCube d m) n hn
            a sigma0 hsigma0 g u s1 s s2 p) := by gcongr
    _ = K * localCoarseGrainingLpRHS (Ccz * Cd * Clc)
          (originCube d m) n hn a sigma0 hsigma0 g u s1 s s2 p := by
          rw [← localCoarseGrainingLpRHS_const_mul]


theorem general_coarse_graining {d : ℕ}
    (p : Homogenization.FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    ∀ hd : 2 ≤ d, ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℤ), ∀ hnm : n < m,
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ (alpha s s1 s2 : ℝ), 0 < alpha →
            ∀ hs1pos : 0 < s1, ∀ hs1s : s1 < s,
              ∀ hss2 : s < s2, ∀ hs2one : s2 < 1,
            ∀ (hs : Homogenization.FractionalOrder)
              (hhs : hs.1 = s)
              (hs2 : Homogenization.FractionalOrder)
              (hhs2 : hs2.1 = s2),
              ∀ g : Homogenization.CubeEuclideanWspField
                  (Homogenization.originCube d m) hs2 p,
                ∀ u v : Homogenization.H1Function
                    (Homogenization.openCubeSet (Homogenization.originCube d m)),
                  Homogenization.Book.Ch03.ABK26.IsForcedEquation
                      (Homogenization.originCube d m)
                      (a.coeffOn (Homogenization.originCube d m)) u g.toField →
                  Homogenization.Book.Ch03.ABK26.IsScalarForcedEquation
                      (Homogenization.originCube d m) alpha v g.toField →
                  Homogenization.Book.Ch03.ABK26.HasH10Difference
                      (Homogenization.originCube d m) u v →
                  ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ)) * alpha) *
                        paperNegativeFractionalDual
                          (Homogenization.originCube d m) hs p
                          (Homogenization.Book.Ch03.ABK26.centeredCubeGradientDifferenceL2Field
                            m u v) +
                      ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
                        paperNegativeFractionalDual
                          (Homogenization.originCube d m) hs p
                          (Homogenization.Book.Ch03.ABK26.centeredCubeFluxDifferenceL2Field
                            m (a.coeffOn (Homogenization.originCube d m)) alpha u v) ≤
                    ENNReal.ofReal
                        (C * Real.rpow s
                          (-1 - (p.conjugate.exponent.toReal)⁻¹) * Real.sqrt alpha) *
                      paperHomogenizationError
                        (Homogenization.originCube d m) n s1 .infinity (.finite 1)
                        a alpha *
                      @Homogenization.Book.Ch03.ABK26.weightedLocalSymmetricEnergyLp d
                        ⟨by omega⟩
                        (Homogenization.originCube d m) n
                        (by simpa [Homogenization.originCube] using hnm.le)
                        (a.coeffOn (Homogenization.originCube d m)) u
                        ⟨s1, hs1pos, by linarith⟩ hs p +
                    ENNReal.ofReal
                        (C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ *
                          Real.rpow 3 (s2 * (n : ℝ))) *
                      (1 + paperHomogenizationError
                        (Homogenization.originCube d m) n (s1 / 2)
                        .infinity (.finite 2) a alpha ^ 2) *
                      paperFractionalSeminorm
                        (Homogenization.originCube d m) hs2 p g.toField := by
  intro hd
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C0, hC0top, hbase⟩ :=
    SubdiffusiveProcess.Providers.Section2.exists_generalCoarseGraining_paperDual_libraryRHS d hd p hp
  let D : ℝ≥0∞ := cubeEuclideanWspOverlapDimensionConstant d
  let Cstar : ℝ≥0∞ := C0 * (1 + D) + 1
  let C : ℝ := Cstar.toReal
  have hDtop : D < ⊤ := cubeEuclideanWspOverlapDimensionConstant_lt_top d
  have hCstartop : Cstar < ⊤ := by
    exact ENNReal.add_lt_top.mpr ⟨
      ENNReal.mul_lt_top hC0top (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hDtop⟩),
      ENNReal.one_lt_top⟩
  have hCstarpos : 0 < Cstar := by
    exact lt_of_lt_of_le zero_lt_one (by simp [Cstar])
  have hCpos : 0 < C := ENNReal.toReal_pos hCstarpos.ne' hCstartop.ne
  refine ⟨C, hCpos, ?_⟩
  intro m n hnm a ha alpha s s1 s2 halpha hs1pos hs1s hss2 hs2one
    hs hhs hs2 hhs2 g u v hu hv hzero
  let s1o : FractionalOrder := ⟨s1, hs1pos, by linarith⟩
  have hg : MemCubeEuclideanFullWsp (originCube d m) hs2 p g.toField :=
    ⟨g.euclideanMemLp, g.euclideanMemWsp⟩
  have hraw := hbase m n hnm s1o hs hs2 (by simpa [s1o, hhs] using hs1s)
    (by simpa [hhs, hhs2] using hss2) (a.coeffOn (originCube d m)) alpha halpha
    g.toField hg u v hu hv hzero
  have hscale0 : 0 ≤ Real.rpow 3 (-s * (m : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hraw' :
      ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ)) * alpha) *
            paperNegativeFractionalDual (originCube d m) hs p
              (centeredCubeGradientDifferenceL2Field m u v) +
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
            paperNegativeFractionalDual (originCube d m) hs p
              (centeredCubeFluxDifferenceL2Field m
                (a.coeffOn (originCube d m)) alpha u v) ≤
        (ENNReal.ofReal s) ^ (-(p.conjugate.exponent.toReal)⁻¹) *
          localCoarseGrainingLpRHS C0 (originCube d m) n
            (by simpa [originCube] using hnm.le)
            (a.coeffOn (originCube d m)) alpha halpha g.toField u s1o hs hs2 p := by
    simpa only [hhs, ENNReal.ofReal_mul hscale0, mul_add, mul_assoc] using hraw
  have hn : n ≤ (originCube d m).scale := by
    simpa [originCube] using hnm.le
  have hspos : 0 < s := lt_trans hs1pos hs1s
  have hs2pos : 0 < s2 := lt_trans hspos hss2
  let b : ℝ≥0∞ := ENNReal.ofReal s
  let b2 : ℝ≥0∞ := ENNReal.ofReal s2
  let pinv : ℝ := (p.exponent.toReal)⁻¹
  let qinv : ℝ := (p.conjugate.exponent.toReal)⁻¹
  have hb0 : b ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hspos
  have hbtop : b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hCeq : ENNReal.ofReal C = Cstar := by
    exact ENNReal.ofReal_toReal hCstartop.ne
  have hC0le : C0 ≤ Cstar := by
    dsimp only [Cstar]
    calc
      C0 = C0 * 1 := by rw [mul_one]
      _ ≤ C0 * (1 + D) := by gcongr; exact le_add_right le_rfl
      _ ≤ C0 * (1 + D) + 1 := le_add_right le_rfl
  have hC0Dle : C0 * D ≤ Cstar := by
    dsimp only [Cstar]
    calc
      C0 * D ≤ C0 * (1 + D) := by gcongr; exact le_add_left le_rfl
      _ ≤ C0 * (1 + D) + 1 := le_add_right le_rfl
  have hpgt : 1 < p.exponent.toReal := by
    rw [← ENNReal.toReal_one,
      ENNReal.toReal_lt_toReal ENNReal.one_ne_top p.lt_top.ne]
    exact p.one_lt
  have hpq : p.exponent.toReal.HolderConjugate
      p.conjugate.exponent.toReal := by
    let : ENNReal.HolderConjugate p.exponent p.conjugate.exponent :=
      p.holderConjugate
    exact ENNReal.HolderConjugate.toReal hpgt
  have hpinv_nonneg : 0 ≤ pinv := by
    exact inv_nonneg.mpr (le_trans zero_le_one hpgt.le)
  have hqinv_nonneg : 0 ≤ qinv := by
    exact inv_nonneg.mpr hpq.symm.pos.le
  have hinvsum : pinv + qinv = 1 := by
    simpa only [pinv, qinv, one_div, inv_one] using hpq.one_div_add_one_div
  have hpow1 : b ^ (-qinv) * b⁻¹ = b ^ (-1 - qinv) := by
    rw [← ENNReal.rpow_neg_one]
    rw [← ENNReal.rpow_add _ _ hb0 hbtop]
    congr 1
    ring
  have hpow2 : b ^ (-qinv) * (b ^ (-(9 / 2 : ℝ)) * b ^ (-pinv)) =
      b ^ (-11 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add _ _ hb0 hbtop,
      ← ENNReal.rpow_add _ _ hb0 hbtop]
    congr 1
    linarith
  have hb2_to_b : b2 ^ (-pinv) ≤ b ^ (-pinv) := by
    dsimp only [b, b2]
    rw [ENNReal.ofReal_rpow_of_pos hs2pos, ENNReal.ofReal_rpow_of_pos hspos]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos hspos (le_of_lt hss2) (neg_nonpos.mpr hpinv_nonneg))
  have hE1 := SubdiffusiveProcess.Providers.Section2.parentTruncatedErrorOne_le_paperHomogenizationError
    (originCube d m) n hn a ha alpha halpha s1o
  have hE2 := SubdiffusiveProcess.Providers.Section2.parentTruncatedErrorTwo_le_paperHomogenizationError
    (originCube d m) n hn a ha alpha halpha (fractionalOrderHalf s1o)
  have hover :=
    SubdiffusiveProcess.Providers.Section2.cubeEuclideanPositiveBesovOverlapESeminorm_le_paperFractionalSeminorm
      (originCube d m) hs2 p g.toCubeEuclideanLpField
  have hsqrt : (ENNReal.ofReal alpha) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt alpha) := by
    rw [ENNReal.ofReal_rpow_of_pos halpha, Real.sqrt_eq_rpow]
  have hCnonneg : 0 ≤ C := hCpos.le
  have hcoef1scalar :
      ENNReal.ofReal (C * Real.rpow s (-1 - qinv) * Real.sqrt alpha) =
        Cstar * b ^ (-1 - qinv) * ENNReal.ofReal alpha ^ (1 / 2 : ℝ) := by
    calc
      ENNReal.ofReal (C * Real.rpow s (-1 - qinv) * Real.sqrt alpha) =
          ENNReal.ofReal (C * Real.rpow s (-1 - qinv)) *
            ENNReal.ofReal (Real.sqrt alpha) :=
        ENNReal.ofReal_mul
          (mul_nonneg hCnonneg (Real.rpow_nonneg hspos.le _))
      _ = ENNReal.ofReal C * ENNReal.ofReal (Real.rpow s (-1 - qinv)) *
            ENNReal.ofReal (Real.sqrt alpha) := by
              rw [ENNReal.ofReal_mul hCnonneg]
      _ = _ := by
        rw [hCeq, ← hsqrt]
        change Cstar * ENNReal.ofReal (s ^ (-1 - qinv)) *
            ENNReal.ofReal alpha ^ (1 / 2 : ℝ) = _
        rw [← ENNReal.ofReal_rpow_of_pos hspos]
  have hcoef1 :
      b ^ (-qinv) * (C0 * b⁻¹ * (ENNReal.ofReal alpha) ^ (1 / 2 : ℝ)) ≤
        ENNReal.ofReal
          (C * Real.rpow s (-1 - qinv) * Real.sqrt alpha) := by
    rw [hcoef1scalar]
    calc
      b ^ (-qinv) * (C0 * b⁻¹ * ENNReal.ofReal alpha ^ (1 / 2 : ℝ)) =
          C0 * (b ^ (-qinv) * b⁻¹) * ENNReal.ofReal alpha ^ (1 / 2 : ℝ) := by ring
      _ = C0 * b ^ (-1 - qinv) * ENNReal.ofReal alpha ^ (1 / 2 : ℝ) := by rw [hpow1]
      _ ≤ Cstar * b ^ (-1 - qinv) * ENNReal.ofReal alpha ^ (1 / 2 : ℝ) := by gcongr
  have hcoef2scalar :
      ENNReal.ofReal (C * Real.rpow s (-11 / 2)) =
        Cstar * b ^ (-11 / 2 : ℝ) := by
    calc
      ENNReal.ofReal (C * Real.rpow s (-11 / 2)) =
          ENNReal.ofReal C * ENNReal.ofReal (Real.rpow s (-11 / 2)) :=
            ENNReal.ofReal_mul hCnonneg
      _ = _ := by
        rw [hCeq]
        change Cstar * ENNReal.ofReal (s ^ (-11 / 2 : ℝ)) = _
        rw [← ENNReal.ofReal_rpow_of_pos hspos]
  have hcoef2 :
      b ^ (-qinv) *
          (C0 * b ^ (-(9 / 2 : ℝ)) * (D * b2 ^ (-pinv))) ≤
        ENNReal.ofReal (C * Real.rpow s (-11 / 2)) := by
    rw [hcoef2scalar]
    calc
      b ^ (-qinv) * (C0 * b ^ (-(9 / 2 : ℝ)) * (D * b2 ^ (-pinv))) ≤
          b ^ (-qinv) * (C0 * b ^ (-(9 / 2 : ℝ)) * (D * b ^ (-pinv))) := by
            gcongr
      _ = (C0 * D) *
          (b ^ (-qinv) * (b ^ (-(9 / 2 : ℝ)) * b ^ (-pinv))) := by ring
      _ = (C0 * D) * b ^ (-11 / 2 : ℝ) := by rw [hpow2]
      _ ≤ Cstar * b ^ (-11 / 2 : ℝ) := by gcongr
  have hover' :
      Homogenization.Book.Ch03.ABK26.cubeEuclideanPositiveBesovOverlapESeminorm
          (originCube d m) hs2 p g.toField ≤
        D * b2 ^ (-pinv) *
          paperFractionalSeminorm (originCube d m) hs2 p g.toField := by
    simpa only [D, b2, pinv, hhs2] using hover
  have hE2' :
      1 + Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
            (originCube d m) n hn (a.coeffOn (originCube d m)) alpha halpha
              (fractionalOrderHalf s1o) ^ 2 ≤
        1 + paperHomogenizationError
            (originCube d m) n (s1 / 2) .infinity (.finite 2) a alpha ^ 2 := by
    have hsq := pow_le_pow_left' hE2 2
    simpa only [s1o, fractionalOrderHalf] using add_le_add le_rfl hsq
  have hforceScalar :
      ENNReal.ofReal
          (C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ *
            Real.rpow 3 (s2 * (n : ℝ))) =
        ENNReal.ofReal (C * Real.rpow s (-11 / 2)) *
          (ENNReal.ofReal (s2 - s))⁻¹ *
          ENNReal.ofReal (Real.rpow 3 (s2 * (n : ℝ))) := by
    have hfirst : 0 ≤ C * Real.rpow s (-11 / 2) :=
      mul_nonneg hCnonneg (Real.rpow_nonneg hspos.le _)
    have hdiffinv : 0 ≤ (s2 - s)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hss2.le)
    calc
      _ = ENNReal.ofReal (C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹) *
          ENNReal.ofReal (Real.rpow 3 (s2 * (n : ℝ))) :=
            ENNReal.ofReal_mul (mul_nonneg hfirst hdiffinv)
      _ = ENNReal.ofReal (C * Real.rpow s (-11 / 2)) *
          ENNReal.ofReal ((s2 - s)⁻¹) *
          ENNReal.ofReal (Real.rpow 3 (s2 * (n : ℝ))) := by
            rw [ENNReal.ofReal_mul hfirst]
      _ = _ := by rw [ENNReal.ofReal_inv_of_pos (sub_pos.mpr hss2)]
  calc
    _ ≤ (ENNReal.ofReal s) ^ (-(p.conjugate.exponent.toReal)⁻¹) *
          localCoarseGrainingLpRHS C0 (originCube d m) n
            (by simpa [originCube] using hnm.le)
            (a.coeffOn (originCube d m)) alpha halpha g.toField u s1o hs hs2 p := hraw'
    _ ≤ _ := by
      unfold localCoarseGrainingLpRHS
      rw [hhs, hhs2]
      rw [mul_add]
      apply add_le_add
      · calc
          b ^ (-qinv) *
                (C0 * b⁻¹ * (ENNReal.ofReal alpha) ^ (1 / 2 : ℝ) *
                    Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                      (originCube d m) n hn (a.coeffOn (originCube d m))
                      alpha halpha s1o *
                  weightedLocalSymmetricEnergyLp (originCube d m) n hn
                    (a.coeffOn (originCube d m)) u s1o hs p) =
              (b ^ (-qinv) *
                (C0 * b⁻¹ * (ENNReal.ofReal alpha) ^ (1 / 2 : ℝ))) *
                  Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                    (originCube d m) n hn (a.coeffOn (originCube d m))
                    alpha halpha s1o *
                weightedLocalSymmetricEnergyLp (originCube d m) n hn
                  (a.coeffOn (originCube d m)) u s1o hs p := by ring
          _ ≤ ENNReal.ofReal
                (C * Real.rpow s (-1 - qinv) * Real.sqrt alpha) *
              paperHomogenizationError (originCube d m) n s1 .infinity (.finite 1)
                a alpha *
              weightedLocalSymmetricEnergyLp (originCube d m) n hn
                (a.coeffOn (originCube d m)) u s1o hs p := by
                  gcongr
          _ = _ := by rfl
      · calc
          b ^ (-qinv) *
                (C0 * b ^ (-(9 / 2 : ℝ)) *
                    (ENNReal.ofReal (s2 - s))⁻¹ *
                    (1 + Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                      (originCube d m) n hn (a.coeffOn (originCube d m))
                      alpha halpha (fractionalOrderHalf s1o) ^ 2) *
                    ENNReal.ofReal (Real.rpow 3 (s2 * (n : ℝ))) *
                  Homogenization.Book.Ch03.ABK26.cubeEuclideanPositiveBesovOverlapESeminorm
                    (originCube d m) hs2 p g.toField) ≤
              ENNReal.ofReal (C * Real.rpow s (-11 / 2)) *
                (ENNReal.ofReal (s2 - s))⁻¹ *
                (1 + paperHomogenizationError
                  (originCube d m) n (s1 / 2) .infinity (.finite 2) a alpha ^ 2) *
                ENNReal.ofReal (Real.rpow 3 (s2 * (n : ℝ))) *
                paperFractionalSeminorm (originCube d m) hs2 p g.toField := by
                  calc
                    _ ≤ b ^ (-qinv) *
                        (C0 * b ^ (-(9 / 2 : ℝ)) *
                          (ENNReal.ofReal (s2 - s))⁻¹ *
                          (1 + Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                            (originCube d m) n hn (a.coeffOn (originCube d m))
                            alpha halpha (fractionalOrderHalf s1o) ^ 2) *
                          ENNReal.ofReal (Real.rpow 3 (s2 * (n : ℝ))) *
                          (D * b2 ^ (-pinv) *
                            paperFractionalSeminorm
                              (originCube d m) hs2 p g.toField)) := by
                                gcongr
                    _ = (b ^ (-qinv) *
                          (C0 * b ^ (-(9 / 2 : ℝ)) * (D * b2 ^ (-pinv)))) *
                        (ENNReal.ofReal (s2 - s))⁻¹ *
                        (1 + Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                          (originCube d m) n hn (a.coeffOn (originCube d m))
                          alpha halpha (fractionalOrderHalf s1o) ^ 2) *
                        ENNReal.ofReal (Real.rpow 3 (s2 * (n : ℝ))) *
                        paperFractionalSeminorm
                          (originCube d m) hs2 p g.toField := by ring
                    _ ≤ _ := by
                      exact mul_le_mul'
                        (mul_le_mul'
                          (mul_le_mul' (mul_le_mul' hcoef2 le_rfl) hE2') le_rfl)
                        le_rfl
          _ = _ := by
            rw [hforceScalar]
            ring

end

end SubdiffusiveProcess.Providers.Section2
