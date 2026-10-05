module

public import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.AhomStarCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.InductionHypothesis
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.TranslatedDefect
public import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower
public import Homogenization.Book.Ch04.Theorems.Expectations
public import Homogenization.Book.Ch04.Theorems.MomentFactorBounds.Apex

@[expose] public section

/-!
# Annealed dual-mean defect for the Section 4 recursion

This file supplies Step 5 of the `p.combine.under.S` bookkeeping table: the
finite-volume annealed inverse-star coefficient differs from its common
infinite-volume limit by at most twice the normalized one-cube mean response.

The decomposition and normalization use the finite-cutoff annealed bounds
together with the existing starred-limit characterization.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open Filter MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem neZero_of_gmcModel {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩

private theorem integrable_cutoffFullBlockAtCube {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (Q : TriadicCube d) :
    Integrable (Ch04.coarseFullBlockMatrixAtCube Q) (aCutoffRestrictionLaw M L) := by
  exact (aCutoffRestrictionLaw_lawCarrier M L)
    |>.integrable_coarseFullBlockMatrixAtCube_of_integrable_factor_observables Q
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : 1 ≤ 2)
      (integrable_LambdaSqCoeffField_pow_aCutoffRestrictionLaw M L Q
        (by norm_num) 2 (by norm_num))
      (integrable_lambdaSqCoeffField_inv_pow_aCutoffRestrictionLaw M L Q
        (by norm_num) 2 (by norm_num))

private theorem expectedJ_eq_annealedResponseJAtScale {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d) :
    expectedJ M L n p q =
      Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (n : ℤ) p q := by
  let f : Sample d → RegCoeffField d := aCutoffRegCoeffField M L
  have htarget : AEStronglyMeasurable
      (Ch04.restrictionResponseJObservableCubeSet (originCube d (n : ℤ)) p q)
      (aCutoffRestrictionLaw M L) :=
    ((aCutoffRestrictionLaw_lawCarrier M L)
      |>.aemeasurable_restrictionResponseJObservableCubeSet
        (originCube d (n : ℤ)) p q).aestronglyMeasurable
  change (∫ omega, J (Ch02.cubeDomain (originCube d (n : ℤ)))
      (aCutoffCoeffOnData M L omega
        (Ch02.cubeDomain (originCube d (n : ℤ)))).toCoeffOn p q
      ∂M.P.toMeasure) =
    ∫ a, Ch04.restrictionResponseJObservableCubeSet
      (originCube d (n : ℤ)) p q a ∂(aCutoffRestrictionLaw M L)
  rw [aCutoffRestrictionLaw_eq_map] at htarget ⊢
  rw [integral_map (measurable_aCutoffRegCoeffField M L).aemeasurable htarget]
  apply integral_congr_ae
  filter_upwards with omega
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let a := (aCutoffCoeffOnData M L omega U).toCoeffOn
  calc
    J U a p q = ResponseJ (openCubeSet (originCube d (n : ℤ))) p q
        (aCutoffRegCoeffField M L omega).toFun := by
      simpa [U, a, aCutoffCoeffOnData, ScalarCoeffOnData.toCoeffOn,
        aCutoffRegCoeffField, Ch02.cubeDomain_coe] using!
        Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ U a p q
    _ = ResponseJ (cubeSet (originCube d (n : ℤ))) p q
        (aCutoffRegCoeffField M L omega).toFun :=
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube
        (originCube d (n : ℤ)) p q _ |>.symm
    _ = _ := rfl

theorem aux_dedup_d136_annealedSigmaStarInvAtScale_eq_abarStarInv {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    Ch04.annealedSigmaStarInvAtScale (aCutoffRestrictionLaw M L) (n : ℤ) =
      abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) := by
  ext i j
  rw [Ch04.annealedSigmaStarInvAtScale, Ch04.annealedSigmaStarInv,
    Ch04.annealedBlockMatrix, abarStarInv, aCutoffRestrictionLaw_eq_map]
  change (∫ a : RegCoeffField d,
      (coarseBlockMatrix (cubeSet (originCube d (n : ℤ))) a.toFun).lowerRight i j
        ∂Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure) =
    (∫ omega, (randomAStarMatrix M L
      (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ ∂M.P.toMeasure) i j
  rw [integral_matrix_apply (integrable_randomAStarMatrix_inv M L
    (Ch02.cubeDomain (originCube d (n : ℤ)))) i j]
  rw [integral_map (measurable_aCutoffRegCoeffField M L).aemeasurable
    (((aCutoffRestrictionLaw_lawCarrier M L)
      |>.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
        (originCube d (n : ℤ)) i j).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with omega
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let hdata := aCutoffCoeffOnData M L omega U
  have hcoarse := isCoarseBlockMatrix_ch02_aCutoff M L omega (originCube d (n : ℤ))
  have hEq : Ch02.coarseBlockMatrix U hdata.toCoeffOn =
      coarseBlockMatrix (openCubeSet (originCube d (n : ℤ)))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) :=
    eq_coarseBlockMatrix_of_isCoarseBlockMatrix hcoarse
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  change (coarseBlockMatrix (openCubeSet (originCube d (n : ℤ)))
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))).lowerRight i j =
    (randomAStarMatrix M L U omega)⁻¹ i j
  rw [← hEq, Ch02.coarseBlockMatrix_lowerRight]
  have hstar : (Ch02.aStarCoarse U hdata.toCoeffOn)⁻¹ =
      Ch02.sigmaStarInvCoarse U hdata.toCoeffOn := by
    rw [hTheory.derived_matrices.2.1]
    unfold Ch02.sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U hdata.toCoeffOn)
  exact congrFun (congrFun hstar.symm i) j

private theorem annealedSigmaStarInvAtScale_eq_abarStarInv {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    Ch04.annealedSigmaStarInvAtScale (aCutoffRestrictionLaw M L) (n : ℤ) =
      abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d136_annealedSigmaStarInvAtScale_eq_abarStarInv (d := d) (M := M) (L := L) (n := n)

noncomputable def annealedDualScalar {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) : ℝ :=
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  let hPrim := Ch04.Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    hP (aCutoffRestrictionLaw_isotropic M L)
      (aCutoffRestrictionLaw_adjoint_invariant M L) (n : ℤ)
  hPrim.barSigmaStarInv

private theorem annealedSigmaStarInvAtScale_eq_smul_one {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    Ch04.annealedSigmaStarInvAtScale (aCutoffRestrictionLaw M L) (n : ℤ) =
      annealedDualScalar M L n • (1 : Mat d) := by
  exact (Ch04.Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    (aCutoffRestrictionLaw_lawCarrier M L)
    (aCutoffRestrictionLaw_isotropic M L)
    (aCutoffRestrictionLaw_adjoint_invariant M L) (n : ℤ)).sigmaStarInv_eq

private theorem annealedDualScalar_eq_abarStarInv_entry {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (i : Fin d) :
    annealedDualScalar M L n =
      abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i := by
  rw [← annealedSigmaStarInvAtScale_eq_abarStarInv M L n,
    annealedSigmaStarInvAtScale_eq_smul_one M L n]
  simp

private theorem vecDot_matVecMul_smul_one {d : ℕ} (c : ℝ) (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  rw [smul_matVecMul, vecDot_smul_right,
    show matVecMul (1 : Mat d) x = x by exact Matrix.one_mulVec x]
  rfl

private theorem annealedResponseJAtScale_eq_scalar {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d) :
    Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (n : ℤ) p q =
      (1 / 2 : ℝ) * (annealedDualScalar M L n * vecNormSq q) - vecDot p q +
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (Ch04.annealedBAtScale
            (aCutoffRestrictionLaw M L) (n : ℤ)) p) := by
  have hquad := (aCutoffRestrictionLaw_lawCarrier M L)
    |>.integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
      (originCube d (n : ℤ)) p q (integrable_cutoffFullBlockAtCube M L _)
  let hPrim := Ch04.Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    (aCutoffRestrictionLaw_lawCarrier M L)
    (aCutoffRestrictionLaw_isotropic M L)
    (aCutoffRestrictionLaw_adjoint_invariant M L) (n : ℤ)
  have hmixed : (Ch04.annealedBlockMatrix (aCutoffRestrictionLaw M L)
      (cubeSet (originCube d (n : ℤ)))).lowerLeft = 0 := by
    simpa [Ch04.annealedSigmaStarInvKappaMeanAtScale,
      Ch04.annealedSigmaStarInvKappaMean] using hPrim.sigmaStarInvKappaMean_eq_zero
  have hlower : (Ch04.annealedBlockMatrix (aCutoffRestrictionLaw M L)
      (cubeSet (originCube d (n : ℤ)))).lowerRight =
      Ch04.annealedSigmaStarInvAtScale (aCutoffRestrictionLaw M L) (n : ℤ) := rfl
  have hupper : (Ch04.annealedBlockMatrix (aCutoffRestrictionLaw M L)
      (cubeSet (originCube d (n : ℤ)))).upperLeft =
      Ch04.annealedBAtScale (aCutoffRestrictionLaw M L) (n : ℤ) := rfl
  rw [hmixed, hlower, hupper, annealedSigmaStarInvAtScale_eq_smul_one M L n,
    vecDot_matVecMul_smul_one] at hquad
  simp only [matVecMul, vecDot, Matrix.zero_apply, zero_mul, mul_zero,
    Finset.sum_const_zero, sub_zero] at hquad
  show ∫ a, Ch04.restrictionResponseJObservableCubeSet
      (originCube d (n : ℤ)) p q a ∂(aCutoffRestrictionLaw M L) = _
  simpa only [vecDot, matVecMul] using hquad

private theorem annealedResponseJAtScale_antitone {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {n m : ℕ}
    (hnm : n ≤ m) (p q : Vec d) :
    Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (m : ℤ) p q ≤
      Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (n : ℤ) p q := by
  exact (aCutoffRestrictionLaw_lawCarrier M L).annealedResponseJAtScale_le
    (aCutoffRestrictionLaw_stationary M L)
    (n := (n : ℤ)) (m := (m : ℤ))
    (by exact_mod_cast (Nat.zero_le n)) (by exact_mod_cast hnm) p q
    ((aCutoffRestrictionLaw_lawCarrier M L)
      |>.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        (originCube d (m : ℤ)) p q
        (integrable_cutoffFullBlockAtCube M L _))
    (fun R _ => (aCutoffRestrictionLaw_lawCarrier M L)
      |>.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        R p q
        (integrable_cutoffFullBlockAtCube M L R))

private theorem annealedDualScalar_antitone {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {n m : ℕ}
    (hnm : n ≤ m) :
    annealedDualScalar M L m ≤ annealedDualScalar M L n := by
  have hBlock := (aCutoffRestrictionLaw_lawCarrier M L)
    |>.blockMatLoewnerLE_annealedBlockMatrixAtScale_of_integrable_coarseFullBlockMatrixAtCube
      (aCutoffRestrictionLaw_stationary M L)
      (n := (n : ℤ)) (m := (m : ℤ))
      (by exact_mod_cast (Nat.zero_le n))
      (by exact_mod_cast hnm)
      (integrable_cutoffFullBlockAtCube M L _)
      (fun R _ => integrable_cutoffFullBlockAtCube M L R)
  have hstar := Ch04.matLoewnerLE_annealedSigmaStarInvAtScale_of_block hBlock
  rw [annealedSigmaStarInvAtScale_eq_smul_one M L m,
    annealedSigmaStarInvAtScale_eq_smul_one M L n] at hstar
  let i : Fin d :=
    ⟨0, lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension⟩
  simpa [i, vecDot_single_left, matVecMul_single] using hstar (Pi.single i 1)

private theorem annealedDualScalar_sub_le_response_sub {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {n m : ℕ}
    (hnm : n ≤ m) (p : Vec d) {q : Vec d} (hq : 0 < vecNormSq q) :
    annealedDualScalar M L n - annealedDualScalar M L m ≤
      2 * (vecNormSq q)⁻¹ *
        (Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (n : ℤ) p q -
          Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (m : ℤ) p q) := by
  have hBlock := (aCutoffRestrictionLaw_lawCarrier M L)
    |>.blockMatLoewnerLE_annealedBlockMatrixAtScale_of_integrable_coarseFullBlockMatrixAtCube
      (aCutoffRestrictionLaw_stationary M L)
      (n := (n : ℤ)) (m := (m : ℤ))
      (by exact_mod_cast (Nat.zero_le n))
      (by exact_mod_cast hnm)
      (integrable_cutoffFullBlockAtCube M L _)
      (fun R _ => integrable_cutoffFullBlockAtCube M L R)
  have hb := Ch04.matLoewnerLE_annealedBAtScale_of_block hBlock p
  have hn := annealedResponseJAtScale_eq_scalar M L n p q
  have hm := annealedResponseJAtScale_eq_scalar M L m p q
  have hmul : (annealedDualScalar M L n - annealedDualScalar M L m) * vecNormSq q ≤
      2 * (Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (n : ℤ) p q -
        Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (m : ℤ) p q) := by
    linarith
  have hne : vecNormSq q ≠ 0 := ne_of_gt hq
  calc
    annealedDualScalar M L n - annealedDualScalar M L m =
        (vecNormSq q)⁻¹ *
          ((annealedDualScalar M L n - annealedDualScalar M L m) * vecNormSq q) := by
      field_simp
    _ ≤ (vecNormSq q)⁻¹ *
        (2 * (Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (n : ℤ) p q -
          Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (m : ℤ) p q)) :=
      mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hq.le)
    _ = _ := by ring

/-- Finite-to-infinite form of the normalized dual-mean comparison. -/
theorem annealedDualScalar_sub_ahom_inv_le_two_mul_meanResponse {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (e : Vec d) (he : vecNormSq e = 1) :
    0 ≤ annealedDualScalar M L n - (ahom M L)⁻¹ ∧
      annealedDualScalar M L n - (ahom M L)⁻¹ ≤
        2 * (ahom M L)⁻¹ * expectedJ M L n
          ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e) := by
  have hahomPos : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L)
  let p := (Real.sqrt (ahom M L))⁻¹ • e
  let q := Real.sqrt (ahom M L) • e
  have hqnorm : vecNormSq q = ahom M L := by
    rw [vecNormSq_smul, he, mul_one, Real.sq_sqrt hahomPos.le]
  have hqpos : 0 < vecNormSq q := hqnorm.symm ▸ hahomPos
  have hlim : Tendsto (fun m : ℕ => annealedDualScalar M L m)
      atTop (nhds (ahom M L)⁻¹) := by
    let i : Fin d :=
      ⟨0, lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension⟩
    have h := tendsto_pi_nhds.mp (tendsto_abarStarInv_originCube M L) i
    have h' := tendsto_pi_nhds.mp h i
    simpa [annealedDualScalar_eq_abarStarInv_entry M L _ i,
      Matrix.one_apply] using h'
  have hnonneg : 0 ≤ annealedDualScalar M L n - (ahom M L)⁻¹ := by
    rw [sub_nonneg]
    exact le_of_tendsto hlim
      (Filter.eventually_atTop.2 ⟨n, fun m hm => annealedDualScalar_antitone M L hm⟩)
  have hfinite : ∀ m : ℕ, n ≤ m →
      annealedDualScalar M L n - annealedDualScalar M L m ≤
        2 * (ahom M L)⁻¹ *
          Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (n : ℤ) p q := by
    intro m hnm
    have hprop := annealedDualScalar_sub_le_response_sub M L hnm p hqpos
    have hJnonneg : 0 ≤
        Ch04.annealedResponseJAtScale (aCutoffRestrictionLaw M L) (m : ℤ) p q :=
      integral_nonneg fun a =>
        Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (m : ℤ)) p q a
    rw [hqnorm] at hprop
    have hinv : 0 ≤ (ahom M L)⁻¹ := inv_nonneg.mpr hahomPos.le
    nlinarith
  refine ⟨hnonneg, ?_⟩
  have htendstoSub : Tendsto
      (fun m : ℕ => annealedDualScalar M L n - annealedDualScalar M L m)
      atTop (nhds (annealedDualScalar M L n - (ahom M L)⁻¹)) :=
    tendsto_const_nhds.sub hlim
  have hle := le_of_tendsto htendstoSub
    (Filter.eventually_atTop.2 ⟨n, fun m hm => hfinite m hm⟩)
  simpa [p, q, expectedJ_eq_annealedResponseJAtScale] using hle

/-- Step 5 with its one-cube mean-response payload exposed.  The explicit
constant is `4`; later assembly may enlarge it to a dimension-only constant. -/
theorem sq_abs_abarStarInv_entry_sub_ahom_inv_le_of_meanResponse {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (e : Vec d) (he : vecNormSq e = 1) {delta1 : ℝ}
    (hmean : expectedJ M L n ((Real.sqrt (ahom M L))⁻¹ • e)
      (Real.sqrt (ahom M L) • e) ≤ delta1) (i : Fin d) :
    |abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i -
        (ahom M L)⁻¹| ^ 2 ≤
      4 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  have hcmp := annealedDualScalar_sub_ahom_inv_le_two_mul_meanResponse
    M L n e he
  rw [← annealedDualScalar_eq_abarStarInv_entry M L n i]
  rw [abs_of_nonneg hcmp.1]
  have hahomPos : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hinv : 0 ≤ (ahom M L)⁻¹ := inv_nonneg.mpr hahomPos.le
  have hupper : annealedDualScalar M L n - (ahom M L)⁻¹ ≤
      2 * (ahom M L)⁻¹ * delta1 := by
    exact hcmp.2.trans (mul_le_mul_of_nonneg_left hmean (mul_nonneg (by norm_num) hinv))
  nlinarith [sq_nonneg (annealedDualScalar M L n - (ahom M L)⁻¹),
    sq_nonneg (2 * (ahom M L)⁻¹ * delta1 -
      (annealedDualScalar M L n - (ahom M L)⁻¹))]

theorem aux_dedup_d203_normalizedDefect_ne_top {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) :
    normalizedDefect M L U omega ≠ ∞ := by
  have heq := paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm
    U (aCutoffCoeffOnData M L omega U).toCoeffOn (ahom M L)
      (normalizedDefectMatrix M L U omega)
      (normalizedDefectMatrix_posSemidef M L U omega)
      (normalizedDefectMatrix_quadratic M L U omega)
  rw [normalizedDefect, heq]
  exact ENNReal.ofReal_ne_top

private theorem normalizedDefect_ne_top {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) :
    normalizedDefect M L U omega ≠ ∞ := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d203_normalizedDefect_ne_top (d := d) (M := M) (L := L) (U := U) (omega := omega)

theorem aux_dedup_d121_paperENNRealLpNorm_eq_eLpNorm_toReal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞}
    (hX : ∀ omega, X omega ≠ ∞) :
    paperENNRealLpNorm mu p X =
      SubdiffusiveProcess.RawLp.eLpNorm (fun omega => (X omega).toReal) (ENNReal.ofReal p) mu := by
  unfold paperENNRealLpNorm
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top]
  · rw [ENNReal.toReal_ofReal hp.le, one_div]
    congr 1
    apply lintegral_congr
    intro omega
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hX omega)]

private theorem paperENNRealLpNorm_eq_eLpNorm_toReal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞}
    (hX : ∀ omega, X omega ≠ ∞) :
    paperENNRealLpNorm mu p X =
      SubdiffusiveProcess.RawLp.eLpNorm (fun omega => (X omega).toReal) (ENNReal.ofReal p) mu := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d121_paperENNRealLpNorm_eq_eLpNorm_toReal (Omega := Omega) (mu := mu) (p := p) (hp := hp) (X := X) (hX := hX)

private theorem integral_normalizedResponse_le_delta_of_inductionHypothesis
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m0 L : ℕ} {xi delta1 : ℝ}
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (e : Vec d) (he : vecNormSq e = 1) :
    expectedJ M L L ((Real.sqrt (ahom M L))⁻¹ • e)
      (Real.sqrt (ahom M L) • e) ≤ delta1 := by
  let U := Ch02.cubeDomain (originCube d (L : ℤ))
  let X : Sample d → ℝ≥0∞ := normalizedDefect M L U
  let Y : Sample d → ℝ := fun omega =>
    J U (aCutoffCoeffOnData M L omega U).toCoeffOn
      ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e)
  have hXm : Measurable X :=
    (measurable_normalizedDefect_potentialShellIndexSigma_Iic M L U).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  have hXtop : ∀ omega, X omega ≠ ∞ := fun omega =>
    normalizedDefect_ne_top M L U omega
  have hYX : ∀ omega, Y omega ≤ (X omega).toReal := by
    intro omega
    have hENN : ENNReal.ofReal (Y omega) ≤ X omega := by
      unfold X Y normalizedDefect paperScalarProbeMaxOn
      exact le_iSup (fun z : {z : Vec d // vecNormSq z = 1} =>
        ENNReal.ofReal (J U (aCutoffCoeffOnData M L omega U).toCoeffOn
          ((Real.sqrt (ahom M L))⁻¹ • (z : Vec d))
          (Real.sqrt (ahom M L) • (z : Vec d)))) ⟨e, he⟩
    exact (ENNReal.ofReal_le_iff_le_toReal (hXtop omega)).mp hENN
  have hnorm : paperENNRealLpNorm M.P.toMeasure xi X ≤ ENNReal.ofReal delta1 := by
    simpa [X, U] using inductionHypothesis_scale_bound hS hLm0
  have hxiPos : 0 < xi := zero_lt_one.trans_le hS.1
  have hLpXi : eLpNorm (fun omega => (X omega).toReal)
      (ENNReal.ofReal xi) M.P.toMeasure ≤ ENNReal.ofReal delta1 := by
    rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hXm.ennreal_toReal.aestronglyMeasurable,
      ← paperENNRealLpNorm_eq_eLpNorm_toReal M.P.toMeasure hxiPos hXtop]
    exact hnorm
  have hOneXi : (1 : ℝ≥0∞) ≤ ENNReal.ofReal xi := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hS.1
  have hLpOne : eLpNorm (fun omega => (X omega).toReal) 1 M.P.toMeasure ≤
      ENNReal.ofReal delta1 :=
    (eLpNorm_le_eLpNorm_of_exponent_le hOneXi).trans
      hLpXi
  have hLpOneTop : eLpNorm (fun omega => (X omega).toReal) 1 M.P.toMeasure < ∞ :=
    hLpOne.trans_lt ENNReal.ofReal_lt_top
  have hXint : Integrable (fun omega => (X omega).toReal) M.P.toMeasure :=
    memLp_one_iff_integrable.mp hLpOneTop
  have hXIntegral : ∫ omega, (X omega).toReal ∂M.P.toMeasure ≤ delta1 := by
    have hEq : ENNReal.ofReal (∫ omega, (X omega).toReal ∂M.P.toMeasure) =
        eLpNorm (fun omega => (X omega).toReal) 1 M.P.toMeasure := by
      rw [eLpNorm_one_eq_lintegral_enorm hXm.ennreal_toReal.aestronglyMeasurable,
        ofReal_integral_eq_lintegral_ofReal hXint
          (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
      apply lintegral_congr
      intro omega
      rw [← ofReal_norm, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg]
    have hof : ENNReal.ofReal (∫ omega, (X omega).toReal ∂M.P.toMeasure) ≤
        ENNReal.ofReal delta1 := hEq.trans_le hLpOne
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hof
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => ENNReal.toReal_nonneg),
      ENNReal.toReal_ofReal hS.2.1.le] at hreal
    exact hreal
  have hYint : Integrable Y M.P.toMeasure := by
    simpa [Y, U] using integrable_cutoffResponseJ M L U
      ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e)
  have hXnonneg : ∀ omega, 0 ≤ (X omega).toReal := fun _ => ENNReal.toReal_nonneg
  calc
    expectedJ M L L ((Real.sqrt (ahom M L))⁻¹ • e)
        (Real.sqrt (ahom M L) • e) = ∫ omega, Y omega ∂M.P.toMeasure := rfl
    _ ≤ ∫ omega, (X omega).toReal ∂M.P.toMeasure :=
      integral_mono hYint hXint hYX
    _ ≤ delta1 := hXIntegral

/-- Source-exact Step 5 payload under the finite induction carrier `S`.
For every `n ≥ L`, each diagonal entry of the isotropic annealed inverse-star
matrix has the printed `4 * ahom⁻² * delta₁²` bound. -/
theorem sq_abs_abarStarInv_entry_sub_ahom_inv_le_of_inductionHypothesis
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m0 L n : ℕ} {xi delta1 : ℝ}
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0) (hLn : L ≤ n)
    (i : Fin d) :
    |abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i -
        (ahom M L)⁻¹| ^ 2 ≤
      4 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  let e : Vec d := Pi.single i 1
  have he : vecNormSq e = 1 := by
    rw [vecNormSq, vecDot_single_left]
    simp [e]
  have hone := integral_normalizedResponse_le_delta_of_inductionHypothesis
    M hS hLm0 e he
  have hchain : expectedJ M L n ((Real.sqrt (ahom M L))⁻¹ • e)
      (Real.sqrt (ahom M L) • e) ≤
      expectedJ M L L ((Real.sqrt (ahom M L))⁻¹ • e)
        (Real.sqrt (ahom M L) • e) := by
    rw [expectedJ_eq_annealedResponseJAtScale,
      expectedJ_eq_annealedResponseJAtScale]
    exact annealedResponseJAtScale_antitone M L hLn _ _
  exact sq_abs_abarStarInv_entry_sub_ahom_inv_le_of_meanResponse
    M L n e he (hchain.trans hone) i

/-- Isotropy makes every off-diagonal entry of the annealed inverse-star
matrix vanish. -/
theorem abarStarInv_originCube_offdiag_eq_zero
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (i j : Fin d) (hij : i ≠ j) :
    abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j = 0 := by
  rw [← annealedSigmaStarInvAtScale_eq_abarStarInv M L n,
    annealedSigmaStarInvAtScale_eq_smul_one M L n]
  simp [hij]

/-- Public finite-to-infinite lower bracket for a diagonal inverse-star
readout.  This is the non-squared half of the dual mean-defect comparison. -/
theorem ahom_inv_le_abarStarInv_originCube_entry
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (i : Fin d) :
    (ahom M L)⁻¹ ≤
      abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i := by
  have h :=
    (annealedDualScalar_sub_ahom_inv_le_two_mul_meanResponse M L n
      (Pi.single i 1) (by simp [vecNormSq, vecDot_single_left])).1
  rw [annealedDualScalar_eq_abarStarInv_entry M L n i] at h
  linarith

/-- Public linear upper half of the inverse-star mean-defect estimate. -/
theorem abarStarInv_originCube_entry_sub_ahom_inv_le_two_mul_meanResponse
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (e : Vec d) (he : vecNormSq e = 1) (i : Fin d) :
    abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i -
        (ahom M L)⁻¹ ≤
      2 * (ahom M L)⁻¹ * expectedJ M L n
        ((Real.sqrt (ahom M L))⁻¹ • e)
        (Real.sqrt (ahom M L) • e) := by
  have h :=
    (annealedDualScalar_sub_ahom_inv_le_two_mul_meanResponse M L n e he).2
  rw [annealedDualScalar_eq_abarStarInv_entry M L n i] at h
  exact h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
