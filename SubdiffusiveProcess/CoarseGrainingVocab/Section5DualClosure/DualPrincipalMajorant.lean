module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualPrefixSuffix
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualBoundaryDiscard
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannFlux

@[expose] public section




open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-! ## Positivity of the random inverse-star matrix -/

/-- The random inverse-star matrix on a cube is positive semidefinite.  Dual
counterpart of `randomAMatrix_posSemidef`. -/
theorem randomAStarMatrixInv_posSemidef {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (U : Ch02.Domain d) :
    ((randomAStarMatrix M L U omega)⁻¹).PosSemidef := by
  rw [randomAStarMatrix_inv_eq_randomSigmaStarInvMatrix]
  exact (Ch02.sigmaStarInvCoarse_posDef U
    (aCutoffCoeffOnData M L omega U).toCoeffOn).posSemidef

/-- The dual quadratic form of the random inverse-star matrix is
nonnegative. -/
theorem vecDot_randomAStarMatrixInv_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (U : Ch02.Domain d) (q : Vec d) :
    0 ≤ vecDot q (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q) :=
  (randomAStarMatrixInv_posSemidef M L omega U).dotProduct_mulVec_nonneg q

/-! ## Dual prefix/suffix integrability -/



theorem integrable_weight_mul_vecDot_randomAStarInv_suffix
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) (U : Ch02.Domain d) (weight : Sample d → ℝ)
    (q : Sample d → Vec d)
    (hweight : @Measurable (Sample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance weight)
    (hq : @Measurable (Sample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance q)
    (hweightedPairInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ weight omega * (q omega i * q omega j))
        M.P.toMeasure) :
    Integrable (fun omega ↦ weight omega * vecDot (q omega)
      (matVecMul ((randomAStarMatrix M n U omega)⁻¹) (q omega)))
      M.P.toMeasure := by
  have hdisjoint : Disjoint (Set.Iic n) (Set.Ioi n) :=
    Set.Iic_disjoint_Ioi le_rfl
  have hAmeas :=
    measurable_randomSigmaStarInvMatrix_potentialShellIndexSigma_Iic M n U
  have hentryMeas : ∀ i j : Fin d,
      @Measurable (Sample d) ℝ
        (potentialShellIndexSigma (Set.Iic n)) inferInstance
        (fun omega ↦ (randomAStarMatrix M n U omega)⁻¹ i j) := by
    intro i j
    have h := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hAmeas)
    simpa only [randomAStarMatrix_inv_eq_randomSigmaStarInvMatrix] using! h
  have hweightedPairMeas : ∀ i j : Fin d,
      @Measurable (Sample d) ℝ
        (potentialShellIndexSigma (Set.Ioi n)) inferInstance
        (fun omega ↦ weight omega * (q omega i * q omega j)) := by
    intro i j
    exact hweight.mul <|
      ((measurable_pi_apply i).comp hq).mul ((measurable_pi_apply j).comp hq)
  have hindep : ∀ i j : Fin d,
      IndepFun (fun omega ↦ (randomAStarMatrix M n U omega)⁻¹ i j)
        (fun omega ↦ weight omega * (q omega i * q omega j))
        M.P.toMeasure := by
    intro i j
    exact indepFun_of_measurable_potentialShellIndexSigma_of_disjoint
      M hdisjoint (hentryMeas i j) (hweightedPairMeas i j)
  have hentryInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ (randomAStarMatrix M n U omega)⁻¹ i j)
        M.P.toMeasure := by
    intro i j
    exact ((integrable_randomAStarMatrix_inv M n U).eval i).eval j
  have htermInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ (randomAStarMatrix M n U omega)⁻¹ i j *
        (weight omega * (q omega i * q omega j))) M.P.toMeasure := by
    intro i j
    exact (hindep i j).integrable_mul (hentryInt i j)
      (hweightedPairInt i j)
  have hquad : (fun omega ↦ weight omega * vecDot (q omega)
      (matVecMul ((randomAStarMatrix M n U omega)⁻¹) (q omega))) =
      fun omega ↦ ∑ i : Fin d, ∑ j : Fin d,
        (randomAStarMatrix M n U omega)⁻¹ i j *
          (weight omega * (q omega i * q omega j)) := by
    funext omega
    simp only [vecDot, matVecMul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hquad]
  exact integrable_finset_sum _ fun i _ ↦
    integrable_finset_sum _ fun j _ ↦ htermInt i j

/-! ## The dual principal majorant -/



def oneStepDualPrincipalMajorant {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d)
    (R : Homogenization.TriadicCube d) (omega : Sample d) (hh : 0 < h) : ℝ :=
  oneStepLowerSourceCellWeight M n h R omega *
    vecDot (oneStepPaperNeumannCellSlope M n h q
      (originCube d (K : ℤ)) R omega hh)
      (matVecMul ((randomAStarMatrix M n (Ch02.cubeDomain R) omega)⁻¹)
        (oneStepPaperNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh))

/-- Pointwise nonnegativity of the dual principal envelope. -/
theorem oneStepDualPrincipalMajorant_nonneg
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (R : Homogenization.TriadicCube d)
    (omega : Sample d) (hh : 0 < h) :
    0 ≤ oneStepDualPrincipalMajorant (K := K) M n h q R omega hh := by
  unfold oneStepDualPrincipalMajorant oneStepLowerSourceCellWeight
  exact mul_nonneg
    (cutoffRatioSup_pos M n (n + h) (Ch02.cubeDomain R) omega).le
    (vecDot_randomAStarMatrixInv_nonneg M n omega (Ch02.cubeDomain R) _)

/-- The measurable dual principal envelope is integrable.  Prefix/suffix
independence is used at the matrix-entry level, after the fresh slope and
reciprocal weight are placed in `L⁴`, `L⁴`, and `L²`. -/
theorem integrable_oneStepDualPrincipalMajorant
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (R : Homogenization.TriadicCube d)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    Integrable (oneStepDualPrincipalMajorant (K := K) M n h q R · hh)
      M.P.toMeasure := by
  let slope : Sample d → Homogenization.Vec d := fun omega ↦
    oneStepPaperNeumannCellSlope M n h q (originCube d (K : ℤ)) R omega hh
  have hpair : ∀ i j : Fin d,
      Integrable (fun omega ↦ oneStepLowerSourceCellWeight M n h R omega *
        (slope omega i * slope omega j)) M.P.toMeasure := fun i j ↦
    integrable_weight_mul_pair_of_memLp_two_four M
      (oneStepLowerSourceCellWeight M n h R) slope
      (memLp_two_oneStepLowerSourceCellWeight M n h R hh)
      (fun k ↦ by
        simpa only [slope] using
          memLp_four_oneStepPaperNeumannCellSlope_coord M n h q
            (originCube d (K : ℤ)) R hh hq k) i j
  simpa only [oneStepDualPrincipalMajorant, slope] using
    integrable_weight_mul_vecDot_randomAStarInv_suffix M n
      (Ch02.cubeDomain R) (oneStepLowerSourceCellWeight M n h R) slope
      (measurable_oneStepLowerSourceCellWeight_potentialShellIndexSigma_Ioi
        M n h R hh)
      (measurable_oneStepPaperNeumannCellSlope_potentialShellIndexSigma_Ioi
        M n h q (originCube d (K : ℤ)) R hh)
      hpair

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
