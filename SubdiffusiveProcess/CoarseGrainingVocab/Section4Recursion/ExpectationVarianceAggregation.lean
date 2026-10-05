module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.CombineGoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ExpectedResponseReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.VarianceInterfaces
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SecondMomentBudgets
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffNormalization
public import Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.Triangle

@[expose] public section

/-!
# Expectation and variance aggregation for the Section 4 recursion

This module carries the finite-sample objects in the good-event estimate to
the literal expected-response bookkeeping used by `p.combine.under.S`.

The carrier is split before applying the deterministic parent/descendant
quadratic estimate.  In the
GMC scalar setting the mixed coarse block vanishes samplewise, so only the
inverse-star channel remains.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators MatrixOrder

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- On the scalar cutoff carrier the comparison vector has no mixed channel. -/
theorem coarseScaleSeparation_aCutoff_eq_randomAStarInv_mulVec_sub
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : Sample d)
    (Q : TriadicCube d) (p q : Vec d) :
    coarseScaleSeparation (aCutoffRegCoeffField M L omega)
        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega) Q p q =
      matVecMul
          ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹) q - p := by
  let U := Ch02.cubeDomain Q
  let hdata := aCutoffCoeffOnData M L omega U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  have hkappa : Ch02.kappaCoarse U hdata.toCoeffOn = 0 := hTheory.kappa_eq_zero
  have hstar : Ch02.sigmaStarInvCoarse U hdata.toCoeffOn =
      (randomAStarMatrix M L U omega)⁻¹ := by
    change Ch02.sigmaStarInvCoarse U hdata.toCoeffOn =
      (Ch02.aStarCoarse U hdata.toCoeffOn)⁻¹
    rw [hTheory.derived_matrices.2.1]
    exact (Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U hdata.toCoeffOn)).symm
  unfold coarseScaleSeparation
  change matVecMul (Ch02.sigmaStarInvCoarse U hdata.toCoeffOn)
      (q + matVecMul (Ch02.kappaCoarse U hdata.toCoeffOn) p) - p = _
  rw [hkappa, hstar]
  have hzero : matVecMul (0 : Mat d) p = 0 := by
    ext i
    simp [matVecMul]
  rw [hzero, add_zero]

/-- The scalar cutoff coarse-matrix variation is literally the inverse-star
matrix difference applied to the load `q`. -/
theorem coarseMatrixVariationSq_aCutoff_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : Sample d)
    (Q R : TriadicCube d) (p q : Vec d) :
    coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega) Q p q R =
      vecNormSq
        (matVecMul
          ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ -
            (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) q) := by
  unfold coarseMatrixVariationSq
  rw [coarseScaleSeparation_aCutoff_eq_randomAStarInv_mulVec_sub,
    coarseScaleSeparation_aCutoff_eq_randomAStarInv_mulVec_sub, sub_matVecMul]
  congr 1
  abel

theorem aux_dedup_d116_restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) (omega : Sample d) :
    Ch04.restrictionResponseJObservableCubeSet R p q
        (aCutoffRegCoeffField M L omega) =
      cutoffResponseOnCube M L p q R omega := by
  unfold cutoffResponseOnCube
  change ResponseJ (cubeSet R) p q (aCutoffRegCoeffField M L omega).toFun =
    J (Ch02.cubeDomain R) ((aCutoffFamily M L omega).coeffOn R) p q
  calc
    ResponseJ (cubeSet R) p q (aCutoffRegCoeffField M L omega).toFun =
        ResponseJ (openCubeSet R) p q (aCutoffRegCoeffField M L omega).toFun :=
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube R p q _
    _ = J (Ch02.cubeDomain R) ((aCutoffFamily M L omega).coeffOn R) p q := by
      simpa [aCutoffFamily, aCutoffTriadicData, aCutoffRegCoeffField,
        aCutoffCoeffOnData, ScalarCoeffOnData.toCoeffOn, Ch02.cubeDomain_coe] using!
        (Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
          (Ch02.cubeDomain R) ((aCutoffFamily M L omega).coeffOn R) p q).symm

private theorem restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) (omega : Sample d) :
    Ch04.restrictionResponseJObservableCubeSet R p q
        (aCutoffRegCoeffField M L omega) =
      cutoffResponseOnCube M L p q R omega := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d116_restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube (d := d) (M := M) (L := L) (p := p) (q := q) (R := R) (omega := omega)

private theorem integrable_restrictionResponseJ_aCutoff
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (R : TriadicCube d)
    (p q : Vec d) :
    Integrable (fun omega : Sample d =>
      Ch04.restrictionResponseJObservableCubeSet R p q
        (aCutoffRegCoeffField M L omega)) M.P.toMeasure := by
  simpa only [restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube M L p q R] using!
    integrable_cutoffResponseOnCube M L p q R

private theorem integral_restrictionResponseJ_originCube_aCutoff_eq_expectedJ
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (p q : Vec d) :
    ∫ omega : Sample d,
        Ch04.restrictionResponseJObservableCubeSet (originCube d (m : ℤ)) p q
          (aCutoffRegCoeffField M L omega) ∂M.P.toMeasure =
      expectedJ M L m p q := by
  simp_rw [restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube M L p q]
  rfl

/-- Stationarity turns the integrated response defect into the literal
`expectedJDifference` used by the combine statement. -/
theorem integral_responseDefectAverageAtScale_aCutoff_eq_expectedJDifference
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ) (hnm : n ≤ m)
    (p q : Vec d) :
    ∫ omega,
        Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
          (m : ℤ) (n : ℤ) p q (aCutoffRegCoeffField M L omega)
        ∂M.P.toMeasure =
      expectedJDifference M L n m p q := by
  let Q := originCube d (m : ℤ)
  let j := (m - n : ℕ)
  have hj : Int.toNat ((m : ℤ) - (n : ℤ)) = j := by omega
  have hscale : ∀ R ∈ descendantsAtDepth Q j, R.scale = (n : ℤ) := by
    intro R hR
    have hnmInt : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast hnm
    have hR' : R ∈ descendantsAtScale Q (n : ℤ) := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hnmInt]
      simpa [Q, j, hj] using! hR
    simpa only [Q] using! scale_eq_of_mem_descendantsAtScale hR'
  have hchildInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (cutoffResponseOnCube M L p q R) M.P.toMeasure := by
    intro R _
    exact integrable_cutoffResponseOnCube M L p q R
  have hparentInt : Integrable (cutoffResponseOnCube M L p q Q) M.P.toMeasure :=
    integrable_cutoffResponseOnCube M L p q Q
  have hpoint : (fun omega =>
      Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
        (m : ℤ) (n : ℤ) p q (aCutoffRegCoeffField M L omega)) =
      fun omega => descendantsAverage Q j
          (fun R => cutoffResponseOnCube M L p q R omega) -
        cutoffResponseOnCube M L p q Q omega := by
    funext omega
    simp only [Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale,
      Q, hj]
    congr 1
    · unfold descendantsAverage
      simp_rw [restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube M L p q]
    · exact restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube M L p q Q omega
  rw [hpoint, integral_sub]
  · have havgInt :
        ∫ omega, descendantsAverage Q j
            (fun R => cutoffResponseOnCube M L p q R omega) ∂M.P.toMeasure =
          descendantsAverage Q j
            (fun R => ∫ omega, cutoffResponseOnCube M L p q R omega
              ∂M.P.toMeasure) := by
      unfold descendantsAverage
      rw [integral_const_mul, integral_finsetSum]
      intro R hR
      exact hchildInt R hR
    rw [havgInt]
    have hstationary : descendantsAverage Q j
        (fun R => ∫ omega, cutoffResponseOnCube M L p q R omega ∂M.P.toMeasure) =
        ∫ omega, cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega
          ∂M.P.toMeasure := by
      rw [Ch05.Section53.JUpperBoundWeakNorms.descendantsAverage_congr_of_eq_on_descendants
        Q j (G := fun _ => ∫ omega, cutoffResponseOnCube M L p q
          (originCube d (n : ℤ)) omega ∂M.P.toMeasure) (by
            intro R hR
            rw [integral_cutoffResponseOnCube_eq_originCube M L p q R,
              hscale R hR])]
      exact descendantsAverage_const Q j _
    rw [hstationary]
    simpa [expectedJ, cutoffResponseOnCube, Q, aCutoffFamily,
      aCutoffTriadicData] using!
      (expectedJDifference_eq_sub_unconditional M L n m p q).symm
  · unfold descendantsAverage
    exact (integrable_finsetSum _ hchildInt).const_mul _
  · exact hparentInt

/-- The response-defect random variable on two natural-number scales is
integrable on the literal potential sample. -/
theorem integrable_responseDefectAverageAtScale_aCutoff
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ) (hnm : n ≤ m)
    (p q : Vec d) :
    Integrable (fun omega : Sample d =>
      Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
        (m : ℤ) (n : ℤ) p q (aCutoffRegCoeffField M L omega))
      M.P.toMeasure := by
  let Q := originCube d (m : ℤ)
  let j := m - n
  have hj : Int.toNat ((m : ℤ) - (n : ℤ)) = j := by omega
  have hchildInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (cutoffResponseOnCube M L p q R) M.P.toMeasure := by
    intro R _
    exact integrable_cutoffResponseOnCube M L p q R
  have hpoint : (fun omega : Sample d =>
      Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
        (m : ℤ) (n : ℤ) p q (aCutoffRegCoeffField M L omega)) =
      fun omega => descendantsAverage Q j
          (fun R => cutoffResponseOnCube M L p q R omega) -
        cutoffResponseOnCube M L p q Q omega := by
    funext omega
    simp only [Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale,
      Q, hj]
    congr 1
    · unfold descendantsAverage
      simp_rw [restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube M L p q]
    · exact restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube M L p q Q omega
  rw [hpoint]
  exact (Integrable.const_mul (integrable_finsetSum _ hchildInt) _).sub
    (integrable_cutoffResponseOnCube M L p q Q)

private theorem integrable_responseDefectAverageAtScale_aCutoff_int
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (n : ℤ)
    (hn0 : 0 ≤ n) (hnm : n ≤ (m : ℤ)) (p q : Vec d) :
    Integrable (fun omega : Sample d =>
      Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
        (m : ℤ) n p q (aCutoffRegCoeffField M L omega)) M.P.toMeasure := by
  have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
  have hnmNat : n.toNat ≤ m := by omega
  simpa only [hcast] using!
    integrable_responseDefectAverageAtScale_aCutoff M L n.toNat m hnmNat p q

private theorem integral_responseDefectAverageAtScale_aCutoff_int_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (n : ℤ)
    (hn0 : 0 ≤ n) (hnm : n ≤ (m : ℤ)) (p q : Vec d) :
    ∫ omega,
        Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
          (m : ℤ) n p q (aCutoffRegCoeffField M L omega)
        ∂M.P.toMeasure =
      expectedJDifference M L n.toNat m p q := by
  have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
  have hnmNat : n.toNat ≤ m := by omega
  simpa only [hcast] using!
    integral_responseDefectAverageAtScale_aCutoff_eq_expectedJDifference
      M L n.toNat m hnmNat p q

private theorem memLp_two_randomAStarInv_entry
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (i j : Fin d) :
    MemLp (fun omega : Sample d =>
      (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j)
      2 M.P.toMeasure := by
  have hmeas :=
    ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain Q)).eval i).eval j).1)
  exact (memLp_two_iff_integrable_sq hmeas).2
    (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain Q) i j)

private theorem integrable_vecNormSq_matVecMul_of_memLp_two_entries
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Ω → Mat d) (q : Vec d)
    (hA : ∀ i j, MemLp (fun omega => A omega i j) 2 μ) :
    Integrable (fun omega => vecNormSq (matVecMul (A omega) q)) μ := by
  simp only [vecNormSq, vecDot, matVecMul]
  apply integrable_finsetSum
  intro i _hi
  have hrow : MemLp (fun omega => ∑ j, A omega i j * q j) 2 μ := by
    have hrow' := memLp_finsetSum' Finset.univ fun j _ => (hA i j).const_mul (q j)
    convert hrow' using 1
    funext omega
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [Pi.pow_apply, pow_two] using!
    (memLp_two_iff_integrable_sq hrow.aestronglyMeasurable).1 hrow

/-- The coarse-matrix variation in the good-event display is globally
integrable on the literal potential sample. -/
theorem integrable_descendantsAverage_coarseMatrixVariationSq_aCutoff
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    Integrable (fun omega : Sample d =>
      descendantsAverage Q j
        (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
          (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
          Q p q)) M.P.toMeasure := by
  unfold descendantsAverage
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro R hR
  rw [show (fun omega : Sample d =>
      coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
        Q p q R) =
      fun omega => vecNormSq
        (matVecMul
          ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ -
            (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) q) by
      funext omega
      exact coarseMatrixVariationSq_aCutoff_eq M L omega Q R p q]
  apply integrable_vecNormSq_matVecMul_of_memLp_two_entries
  intro i k
  exact (memLp_two_randomAStarInv_entry M L Q i k).sub
    (memLp_two_randomAStarInv_entry M L R i k)

/-- The parent comparison-vector square in the good-event display is globally
integrable on the literal potential sample. -/
theorem integrable_vecNormSq_coarseScaleSeparation_aCutoff
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (p q : Vec d) :
    Integrable (fun omega : Sample d =>
      vecNormSq
        (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
          (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
          Q p q)) M.P.toMeasure := by
  rw [show (fun omega : Sample d =>
      vecNormSq
        (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
          (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
          Q p q)) =
      fun omega => vecNormSq
        (matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹) q - p) by
      funext omega
      rw [coarseScaleSeparation_aCutoff_eq_randomAStarInv_mulVec_sub]]
  have hmat : MemLp (fun omega =>
      matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹) q)
      2 M.P.toMeasure := by
    apply MemLp.of_eval
    intro i
    have hrow := memLp_finsetSum' Finset.univ fun j _ =>
      (memLp_two_randomAStarInv_entry M L Q i j).const_mul (q j)
    convert hrow using 1
    funext omega
    simp only [matVecMul, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hvec : MemLp (fun omega =>
      matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹) q - p)
      2 M.P.toMeasure := hmat.sub (memLp_const p)
  simpa only [vecNormSq, vecDot, Pi.sub_apply, pow_two] using!
    integrable_finsetSum Finset.univ fun i _ =>
      (memLp_two_iff_integrable_sq (hvec.eval i).aestronglyMeasurable).1
        (hvec.eval i)

private theorem integrable_weighted_responseDefect_sum
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (p q : Vec d) :
    Integrable (fun omega : Sample d =>
      ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
        (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
          Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p q (aCutoffRegCoeffField M L omega)) M.P.toMeasure := by
  apply integrable_finsetSum
  intro n hn
  obtain ⟨hnL, hnm⟩ := Finset.mem_Icc.mp hn
  have hn0 : 0 ≤ n := le_trans (Int.ofNat_zero.le.trans (by exact_mod_cast (Nat.zero_le L))) hnL
  exact (integrable_responseDefectAverageAtScale_aCutoff_int
    M L m n hn0 hnm p q).const_mul _

private theorem integral_weighted_responseDefect_sum_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (p q : Vec d) :
    ∫ omega : Sample d,
        ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
          (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
            Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p q (aCutoffRegCoeffField M L omega)
        ∂M.P.toMeasure =
      ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
        (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
          expectedJDifference M L n.toNat m p q := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hnL, hnm⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := le_trans (Int.ofNat_zero.le.trans (by exact_mod_cast (Nat.zero_le L))) hnL
    rw [integral_const_mul,
      integral_responseDefectAverageAtScale_aCutoff_int_eq M L m n hn0 hnm]
  · intro n hn
    obtain ⟨hnL, hnm⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := le_trans (Int.ofNat_zero.le.trans (by exact_mod_cast (Nat.zero_le L))) hnL
    exact (integrable_responseDefectAverageAtScale_aCutoff_int
      M L m n hn0 hnm p q).const_mul _

private theorem integrable_weighted_coarseMatrixVariation_sum
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (p q : Vec d) :
    Integrable (fun omega : Sample d =>
      ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
        (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
          descendantsAverage (originCube d (m : ℤ)) ((m : ℤ) - n).toNat
            (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              (originCube d (m : ℤ)) p q)) M.P.toMeasure := by
  apply integrable_finsetSum
  intro n _hn
  exact (integrable_descendantsAverage_coarseMatrixVariationSq_aCutoff
    M L (originCube d (m : ℤ)) ((m : ℤ) - n).toNat p q).const_mul _

private theorem integral_weighted_coarseMatrixVariation_sum_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (p q : Vec d) :
    ∫ omega : Sample d,
        ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
          (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
            descendantsAverage (originCube d (m : ℤ)) ((m : ℤ) - n).toNat
              (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                (originCube d (m : ℤ)) p q)
        ∂M.P.toMeasure =
      ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
        (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
          ∫ omega : Sample d,
            descendantsAverage (originCube d (m : ℤ)) ((m : ℤ) - n).toNat
              (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                (originCube d (m : ℤ)) p q)
            ∂M.P.toMeasure := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _hn
    rw [integral_const_mul]
  · intro n _hn
    exact (integrable_descendantsAverage_coarseMatrixVariationSq_aCutoff
      M L (originCube d (m : ℤ)) ((m : ℤ) - n).toNat p q).const_mul _

private theorem sum_Icc_int_weighted_toNat_eq_sum_Icc_nat
    (L m : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
        (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) * F n.toNat =
      ∑ n ∈ Finset.Icc L m,
        Real.rpow 3 (-((m - n : ℕ) : ℝ)) * F n := by
  classical
  refine Finset.sum_bij (fun n _ => n.toNat) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnL, hnm⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := by omega
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
    apply Finset.mem_Icc.mpr
    constructor
    · change L ≤ n.toNat
      exact_mod_cast hcast.symm ▸ hnL
    · change n.toNat ≤ m
      exact_mod_cast hcast.symm ▸ hnm
  · intro a ha b hb hab
    obtain ⟨haL, _ham⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hbL, _hbm⟩ := Finset.mem_Icc.mp hb
    have ha0 : 0 ≤ a := by omega
    have hb0 : 0 ≤ b := by omega
    change a.toNat = b.toNat at hab
    have hacast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
    have hbcast : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0
    omega
  · intro n hn
    refine ⟨(n : ℤ), ?_, by simp⟩
    simpa using! hn
  · intro n hn
    obtain ⟨hnL, hnm⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := by omega
    have hdiff : (((m : ℤ) - n : ℤ) : ℝ) = ((m - n.toNat : ℕ) : ℝ) := by
      congr 1
      omega
    change (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) * F n.toNat =
      Real.rpow 3 (-((m - n.toNat : ℕ) : ℝ)) * F n.toNat
    rw [hdiff]
    rfl

/-- The Chapter 5 two-plus-eight estimate pulled all the way back from the
canonically normalized restriction law to the literal GMC potential sample.
This removes the measure-carrier part of the finite-sample seam; the remaining
specialization is deterministic dilation and block readout. -/
theorem fullBlock_two_plus_eight_rescaled_aCutoff_ae
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (center : ℤ) (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    (fun omega : Sample d =>
      Ch05.Section56.fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
        ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
          (aCutoffNormalizationDepth d L))
        (aCutoffNormalization_structuralLaw M L)
        center S Q
        (rescaleReg (aCutoffNormalizationDepth d L)
          (aCutoffRegCoeffField M L omega)))
      ≤ᵐ[M.P.toMeasure]
    fun omega : Sample d =>
      2 * Ch05.Section56.descendantsAverageFluctuationOperatorNormSqWithNormalizer
        ((aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
          (aCutoffNormalizationDepth d L))
        (aCutoffNormalization_structuralLaw M L)
        center S Q j
        (rescaleReg (aCutoffNormalizationDepth d L)
          (aCutoffRegCoeffField M L omega)) +
      8 * Ch05.Section56.blockJTraceAverageSqWithNormalizers S T Q j
        (rescaleReg (aCutoffNormalizationDepth d L)
          (aCutoffRegCoeffField M L omega)) := by
  let k := aCutoffNormalizationDepth d L
  let P := aCutoffRestrictionLaw M L
  let hP : Ch04.RestrictionLawCarrier P := aCutoffRestrictionLaw_lawCarrier M L
  let hStruct : Ch04.RestrictionStructuralLaw
      (Ch04.restrictionScaleNormalizedLaw k P) :=
    aCutoffNormalization_structuralLaw M L
  have hnormalized :=
    Ch05.Section56.fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_le_two_descendantsAverageWithNormalizer_add_eight_blockJTraceAverageSqWithNormalizers_ae
      (hP.scaleNormalized k) hStruct center S T Q j
  have hnormalizedMap :
      (fun a : RegCoeffField d =>
        Ch05.Section56.fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
          (hP.scaleNormalized k) hStruct center S Q a)
        ≤ᵐ[Measure.map (rescaleReg k) P]
      fun a : RegCoeffField d =>
        2 * Ch05.Section56.descendantsAverageFluctuationOperatorNormSqWithNormalizer
          (hP.scaleNormalized k) hStruct center S Q j a +
        8 * Ch05.Section56.blockJTraceAverageSqWithNormalizers S T Q j a := by
    rw [← Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg]
    exact hnormalized
  have hpullP := ae_of_ae_map
    (measurable_rescaleReg (d := d) k).aemeasurable hnormalizedMap
  have hpullMap :
      (fun a : RegCoeffField d =>
        Ch05.Section56.fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
          (hP.scaleNormalized k) hStruct center S Q (rescaleReg k a))
        ≤ᵐ[Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure]
      fun a : RegCoeffField d =>
        2 * Ch05.Section56.descendantsAverageFluctuationOperatorNormSqWithNormalizer
          (hP.scaleNormalized k) hStruct center S Q j (rescaleReg k a) +
        8 * Ch05.Section56.blockJTraceAverageSqWithNormalizers S T Q j
          (rescaleReg k a) := by
    rw [← aCutoffRestrictionLaw_eq_map]
    exact hpullP
  have hpullSample := ae_of_ae_map
    (measurable_aCutoffRegCoeffField M L).aemeasurable hpullMap
  simpa only [k, P, hP, hStruct] using! hpullSample

/-- Indicator splitting and stationarity turn the samplewise good-event
estimate into the literal expected-response and expected-response-difference
bookkeeping.  The two remaining global quadratic integrals are deliberately
left visible: they are the finite-sample variance aggregation seam. -/
theorem exists_expectedJ_le_integrated_preVarianceSplitDisplay
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ),
        0 < m →
        L ≤ m - 1 →
        C * (3 : ℝ) ^ (-(3 / 4 : ℝ) * (((m : ℤ) - (L : ℤ) : ℤ) : ℝ)) ≤ 1 / 4 →
        ∀ p q : Vec d,
          expectedJ M L m p q ≤
            2 * C * (∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
              (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
                expectedJDifference M L n.toNat m p q) +
            2 * C * (ahom M L *
              ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
                (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
                  ∫ omega : Sample d,
                    descendantsAverage (originCube d (m : ℤ)) ((m : ℤ) - n).toNat
                      (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                        (originCube d (m : ℤ)) p q)
                    ∂M.P.toMeasure) +
            2 * C * (ahom M L *
              ∫ omega : Sample d,
                vecNormSq
                  (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
                    (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                    (originCube d (m : ℤ)) p q)
                ∂M.P.toMeasure) +
            2 * ∫ omega : Sample d in (coarseEllipticityGoodEvent M L m)ᶜ,
              Ch04.restrictionResponseJObservableCubeSet
                (originCube d ((m : ℤ) - 1)) p q
                (aCutoffRegCoeffField M L omega) ∂M.P.toMeasure := by
  obtain ⟨C, hC, hsample⟩ :=
    exists_coarseEllipticityGoodEvent_restrictionResponseJ_le_preVarianceSplitDisplay d
  refine ⟨C, hC, ?_⟩
  intro M L m hm hLm hsmall p q
  let G : Set (Sample d) := coarseEllipticityGoodEvent M L m
  let Jprev : Sample d → ℝ := fun omega =>
    Ch04.restrictionResponseJObservableCubeSet
      (originCube d ((m : ℤ) - 1)) p q (aCutoffRegCoeffField M L omega)
  let Jcur : Sample d → ℝ := fun omega =>
    Ch04.restrictionResponseJObservableCubeSet
      (originCube d (m : ℤ)) p q (aCutoffRegCoeffField M L omega)
  let D : Sample d → ℝ := fun omega =>
    ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
      (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
        Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
          (m : ℤ) n p q (aCutoffRegCoeffField M L omega)
  let V : Sample d → ℝ := fun omega =>
    ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
      (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
        descendantsAverage (originCube d (m : ℤ)) ((m : ℤ) - n).toNat
          (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
            (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
            (originCube d (m : ℤ)) p q)
  let S : Sample d → ℝ := fun omega =>
    vecNormSq
      (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
        (originCube d (m : ℤ)) p q)
  let RHS : Sample d → ℝ := fun omega =>
    1 / 2 * Jcur omega + C * D omega +
      C * (ahom M L * V omega) + C * (ahom M L * S omega)
  have hG : MeasurableSet G := measurableSet_coarseEllipticityGoodEvent M L m
  have hJprev : Integrable Jprev M.P.toMeasure := by
    exact integrable_restrictionResponseJ_aCutoff M L
      (originCube d ((m : ℤ) - 1)) p q
  have hJcur : Integrable Jcur M.P.toMeasure := by
    exact integrable_restrictionResponseJ_aCutoff M L (originCube d (m : ℤ)) p q
  have hD : Integrable D M.P.toMeasure :=
    integrable_weighted_responseDefect_sum M L m p q
  have hV : Integrable V M.P.toMeasure :=
    integrable_weighted_coarseMatrixVariation_sum M L m p q
  have hS : Integrable S M.P.toMeasure :=
    integrable_vecNormSq_coarseScaleSeparation_aCutoff M L
      (originCube d (m : ℤ)) p q
  have hRHS : Integrable RHS M.P.toMeasure :=
    (((hJcur.const_mul _).add (hD.const_mul _)).add
      ((hV.const_mul _).const_mul _)).add ((hS.const_mul _).const_mul _)
  have hsample' : ∀ᵐ omega ∂M.P.toMeasure, omega ∈ G → Jprev omega ≤ RHS omega := by
    simpa only [G, Jprev, Jcur, D, V, S, RHS] using! hsample M L m hm hLm hsmall p q
  have hRHSnonneg : 0 ≤ᵐ[M.P.toMeasure] RHS := by
    filter_upwards [] with omega
    have hJ0 : 0 ≤ Jcur omega :=
      Ch04.restrictionResponseJObservableCubeSet_nonneg _ p q _
    have hD0 : 0 ≤ D omega := by
      dsimp only [D]
      exact Finset.sum_nonneg fun n _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
          (aCutoffRegCoeffField M L omega)
          (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
          (m : ℤ) n p q)
    have hV0 : 0 ≤ V omega := by
      dsimp only [V]
      exact Finset.sum_nonneg fun n _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (descendantsAverage_nonneg _ _ _ fun R _ =>
          coarseMatrixVariationSq_nonneg _ _ _ p q R)
    have hS0 : 0 ≤ S omega := vecNormSq_nonneg _
    have hhom0 : 0 ≤ ahom M L := (ahom_pos M L).le
    dsimp only [RHS]
    positivity
  have hgood : ∫ omega in G, Jprev omega ∂M.P.toMeasure ≤
      ∫ omega in G, RHS omega ∂M.P.toMeasure :=
    setIntegral_mono_on_ae hJprev.integrableOn hRHS.integrableOn hG hsample'
  have hgoodFull : ∫ omega in G, Jprev omega ∂M.P.toMeasure ≤
      ∫ omega, RHS omega ∂M.P.toMeasure :=
    hgood.trans (setIntegral_le_integral hRHS hRHSnonneg)
  have hsplit : ∫ omega, Jprev omega ∂M.P.toMeasure =
      (∫ omega in G, Jprev omega ∂M.P.toMeasure) +
        ∫ omega in Gᶜ, Jprev omega ∂M.P.toMeasure := by
    exact (integral_add_compl hG hJprev).symm
  have hJcurEq : ∫ omega, Jcur omega ∂M.P.toMeasure = expectedJ M L m p q :=
    integral_restrictionResponseJ_originCube_aCutoff_eq_expectedJ M L m p q
  have hJprevEq : ∫ omega, Jprev omega ∂M.P.toMeasure = expectedJ M L (m - 1) p q := by
    have hscale : (((m - 1 : ℕ) : ℤ)) = (m : ℤ) - 1 := by omega
    simpa only [Jprev, hscale] using!
      integral_restrictionResponseJ_originCube_aCutoff_eq_expectedJ M L (m - 1) p q
  have hDEq : ∫ omega, D omega ∂M.P.toMeasure =
      ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
        (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
          expectedJDifference M L n.toNat m p q :=
    integral_weighted_responseDefect_sum_eq M L m p q
  have hVEq : ∫ omega, V omega ∂M.P.toMeasure =
      ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
        (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
          ∫ omega : Sample d,
            descendantsAverage (originCube d (m : ℤ)) ((m : ℤ) - n).toNat
              (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                (originCube d (m : ℤ)) p q)
            ∂M.P.toMeasure :=
    integral_weighted_coarseMatrixVariation_sum_eq M L m p q
  have hRHSint : ∫ omega, RHS omega ∂M.P.toMeasure =
      1 / 2 * expectedJ M L m p q +
        C * (∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
          (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
            expectedJDifference M L n.toNat m p q) +
        C * (ahom M L *
          ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
            (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
              ∫ omega : Sample d,
                descendantsAverage (originCube d (m : ℤ)) ((m : ℤ) - n).toNat
                  (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                    (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                    (originCube d (m : ℤ)) p q)
                ∂M.P.toMeasure) +
        C * (ahom M L * ∫ omega, S omega ∂M.P.toMeasure) := by
    have hJC : Integrable (fun omega => 1 / 2 * Jcur omega) M.P.toMeasure :=
      hJcur.const_mul _
    have hCD : Integrable (fun omega => C * D omega) M.P.toMeasure := hD.const_mul _
    have hCV : Integrable (fun omega => C * (ahom M L * V omega)) M.P.toMeasure :=
      (hV.const_mul _).const_mul _
    have hCS : Integrable (fun omega => C * (ahom M L * S omega)) M.P.toMeasure :=
      (hS.const_mul _).const_mul _
    have hAS : ∫ omega, ahom M L * S omega ∂M.P.toMeasure =
        ahom M L * ∫ omega, S omega ∂M.P.toMeasure := by
      rw [integral_const_mul]
    dsimp only [RHS]
    have h1 : ∫ omega, 1 / 2 * Jcur omega + C * D omega ∂M.P.toMeasure =
        (∫ omega, 1 / 2 * Jcur omega ∂M.P.toMeasure) +
          ∫ omega, C * D omega ∂M.P.toMeasure := integral_add hJC hCD
    have h2 : ∫ omega,
        (1 / 2 * Jcur omega + C * D omega) + C * (ahom M L * V omega)
          ∂M.P.toMeasure =
        (∫ omega, 1 / 2 * Jcur omega + C * D omega ∂M.P.toMeasure) +
          ∫ omega, C * (ahom M L * V omega) ∂M.P.toMeasure :=
      integral_add (hJC.add hCD) hCV
    have h3 : ∫ omega,
        ((1 / 2 * Jcur omega + C * D omega) + C * (ahom M L * V omega)) +
          C * (ahom M L * S omega) ∂M.P.toMeasure =
        (∫ omega,
          (1 / 2 * Jcur omega + C * D omega) + C * (ahom M L * V omega)
            ∂M.P.toMeasure) +
          ∫ omega, C * (ahom M L * S omega) ∂M.P.toMeasure :=
      integral_add ((hJC.add hCD).add hCV) hCS
    rw [h3, h2, h1,
      integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, hJcurEq, hDEq, hVEq, hAS]
  have hpre : expectedJ M L m p q ≤
      1 / 2 * expectedJ M L m p q +
        C * (∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
          (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
            expectedJDifference M L n.toNat m p q) +
        C * (ahom M L *
          ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
            (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
              ∫ omega : Sample d,
                descendantsAverage (originCube d (m : ℤ)) ((m : ℤ) - n).toNat
                  (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                    (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                    (originCube d (m : ℤ)) p q)
                ∂M.P.toMeasure) +
        C * (ahom M L * ∫ omega, S omega ∂M.P.toMeasure) +
        ∫ omega in Gᶜ, Jprev omega ∂M.P.toMeasure := by
    calc
      expectedJ M L m p q ≤ expectedJ M L (m - 1) p q :=
        expectedJ_le_previous M L m p q
      _ = ∫ omega, Jprev omega ∂M.P.toMeasure := hJprevEq.symm
      _ = (∫ omega in G, Jprev omega ∂M.P.toMeasure) +
          ∫ omega in Gᶜ, Jprev omega ∂M.P.toMeasure := hsplit
      _ ≤ (∫ omega, RHS omega ∂M.P.toMeasure) +
          ∫ omega in Gᶜ, Jprev omega ∂M.P.toMeasure :=
        add_le_add hgoodFull (le_refl _)
      _ = _ := by rw [hRHSint]
  dsimp only [S, G, Jprev] at hpre ⊢
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
