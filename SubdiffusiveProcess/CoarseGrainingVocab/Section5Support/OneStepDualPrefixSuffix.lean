import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFinalSpecialization
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.AnnealedDualMeanDefect




open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped Matrix.Norms.Elementwise

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

theorem randomAStarMatrix_inv_eq_randomSigmaStarInvMatrix
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) (U : Ch02.Domain d) (omega : Sample d) :
    (randomAStarMatrix M n U omega)⁻¹ =
      randomSigmaStarInvMatrix M n U omega := by
  let hdata := aCutoffCoeffOnData M n omega U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  change (aStarMatrix U hdata.toCoeffOn)⁻¹ =
    Ch02.sigmaStarInvCoarse U hdata.toCoeffOn
  rw [show aStarMatrix U hdata.toCoeffOn = Ch02.aStarCoarse U hdata.toCoeffOn
    by rfl, hTheory.derived_matrices.2.1]
  unfold Ch02.sigmaStarCoarse
  exact Matrix.nonsing_inv_nonsing_inv _
    (Ch02.isUnit_det_sigmaStarInvCoarse U hdata.toCoeffOn)

/-- Exact weighted factorization for the inverse-star prefix matrix and a
fresh-shell scalar/vector pair. -/
theorem integral_weight_mul_vecDot_randomAStarInv_suffix_eq
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
    ∫ omega, weight omega * vecDot (q omega)
        (matVecMul ((randomAStarMatrix M n U omega)⁻¹) (q omega))
        ∂M.P.toMeasure =
      ∑ i : Fin d, ∑ j : Fin d,
        abarStarInv M n U i j *
          ∫ omega, weight omega * (q omega i * q omega j)
            ∂M.P.toMeasure := by
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
    simpa only [randomAStarMatrix_inv_eq_randomSigmaStarInvMatrix] using h
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
  rw [hquad, integral_finset_sum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [integral_finset_sum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _hj
      rw [(hindep i j).integral_fun_mul_eq_mul_integral
        ((hentryMeas i j).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Iic n))
          le_rfl).aestronglyMeasurable
        ((hweightedPairMeas i j).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n))
          le_rfl).aestronglyMeasurable]
      rw [abarStarInv, Homogenization.integral_matrix_apply
        (integrable_randomAStarMatrix_inv M n U) i j]
    · exact fun j _hj ↦ htermInt i j
  · intro i _hi
    exact integrable_finset_sum Finset.univ fun j _hj ↦ htermInt i j

/-- Scalar selected by the G3 isotropy of the annealed inverse-star block. -/
noncomputable def oneStepAnnealedDualReadout
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n k : ℕ) : ℝ :=
  let hP := aCutoffRestrictionLaw_lawCarrier M n
  let hPrim := Ch04.Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    hP (aCutoffRestrictionLaw_isotropic M n)
      (aCutoffRestrictionLaw_adjoint_invariant M n) (k : ℤ)
  hPrim.barSigmaStarInv

private theorem annealedSigmaStarInvAtScale_eq_abarStarInv_oneStep
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n k : ℕ) :
    Ch04.annealedSigmaStarInvAtScale (aCutoffRestrictionLaw M n) (k : ℤ) =
      abarStarInv M n (Ch02.cubeDomain (originCube d (k : ℤ))) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d136_annealedSigmaStarInvAtScale_eq_abarStarInv (d := d) (M := M) (L := n) (n := k)

theorem abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n k : ℕ) :
    abarStarInv M n (Ch02.cubeDomain (originCube d (k : ℤ))) =
      oneStepAnnealedDualReadout M n k • (1 : Mat d) := by
  rw [← annealedSigmaStarInvAtScale_eq_abarStarInv_oneStep M n k]
  exact (Ch04.Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    (aCutoffRestrictionLaw_lawCarrier M n)
    (aCutoffRestrictionLaw_isotropic M n)
    (aCutoffRestrictionLaw_adjoint_invariant M n) (k : ℤ)).sigmaStarInv_eq

/-- The scalar inverse-star readout is nonnegative. -/
theorem oneStepAnnealedDualReadout_nonneg
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n k : ℕ) :
    0 ≤ oneStepAnnealedDualReadout M n k := by
  let i : Fin d := Classical.choice inferInstance
  have hmatrix :=
    abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one M n k
  have hentry := congrArg (fun A : Mat d ↦ A i i) hmatrix
  have hpoint : ∀ omega,
      0 ≤ (randomAStarMatrix M n
        (Ch02.cubeDomain (originCube d (k : ℤ))) omega)⁻¹ i i := by
    intro omega
    rw [randomAStarMatrix_inv_eq_randomSigmaStarInvMatrix]
    exact (Ch02.sigmaStarInvCoarse_posDef
      (Ch02.cubeDomain (originCube d (k : ℤ)))
      (aCutoffCoeffOnData M n omega
        (Ch02.cubeDomain (originCube d (k : ℤ)))).toCoeffOn).posSemidef.diag_nonneg
  have hintegral : 0 ≤ ∫ omega,
      (randomAStarMatrix M n
        (Ch02.cubeDomain (originCube d (k : ℤ))) omega)⁻¹ i i
        ∂M.P.toMeasure := integral_nonneg hpoint
  change (∫ omega,
      (randomAStarMatrix M n
        (Ch02.cubeDomain (originCube d (k : ℤ))) omega)⁻¹
        ∂M.P.toMeasure) i i = _ at hentry
  rw [Homogenization.integral_matrix_apply
    (integrable_randomAStarMatrix_inv M n
      (Ch02.cubeDomain (originCube d (k : ℤ)))) i i] at hentry
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    if_true, mul_one] at hentry
  rw [← hentry]
  exact hintegral

/-- The annealed inverse-star matrix on a translated triadic cube is the
same scalar matrix as on the centered cube of the same scale. -/
theorem abarStarInv_cube_eq_annealedDualScalar_smul_one
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ)
    (Q : TriadicCube d) (hQscale : 0 ≤ Q.scale) :
    abarStarInv M n (Ch02.cubeDomain Q) =
      oneStepAnnealedDualReadout M n Q.scale.toNat • (1 : Mat d) := by
  let k := Q.scale.toNat
  change abarStarInv M n (Ch02.cubeDomain Q) =
    oneStepAnnealedDualReadout M n k • (1 : Mat d)
  have hscale : ((k : ℕ) : ℤ) = Q.scale := by
    dsimp only [k]
    rw [Int.toNat_of_nonneg hQscale]
  have hcenter :
      abarStarInv M n (Ch02.cubeDomain (originCube d (k : ℤ))) =
        oneStepAnnealedDualReadout M n k • (1 : Mat d) :=
    abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one M n k
  ext i j
  rw [abarStarInv, Homogenization.integral_matrix_apply
    (integrable_randomAStarMatrix_inv M n (Ch02.cubeDomain Q)) i j]
  rw [integral_randomAStarInv_entry_cube_eq_originCube M n Q i j]
  rw [← hscale]
  rw [← Homogenization.integral_matrix_apply
    (integrable_randomAStarMatrix_inv M n
      (Ch02.cubeDomain (originCube d (k : ℤ)))) i j]
  change abarStarInv M n (Ch02.cubeDomain (originCube d (k : ℤ))) i j = _
  rw [hcenter]

/-- Weighted dual source-cell factorization with the correct inverse-star
annealed scalar. -/
theorem integral_lowerWeight_mul_neumannSourceCellSlope_randomAStarInv_eq
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (R : TriadicCube d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    ∫ omega,
        oneStepLowerSourceCellWeight M n h R omega *
          vecDot (oneStepNeumannCellSlope M n h q
            (originCube d (K : ℤ)) R omega hh)
            (matVecMul ((randomAStarMatrix M n (Ch02.cubeDomain R) omega)⁻¹)
              (oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh))
        ∂M.P.toMeasure =
      oneStepAnnealedDualReadout M n (oneStepLocalizationScale n M.delta) *
        ∫ omega,
          oneStepLowerSourceCellWeight M n h R omega *
            vecNormSq (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh)
          ∂M.P.toMeasure := by
  rw [integral_weight_mul_vecDot_randomAStarInv_suffix_eq
    M n (Ch02.cubeDomain R)
      (oneStepLowerSourceCellWeight M n h R)
      (oneStepNeumannCellSlope M n h q (originCube d (K : ℤ)) R · hh)
      (measurable_oneStepLowerSourceCellWeight_potentialShellIndexSigma_Ioi
        M n h R hh)
      (measurable_oneStepNeumannCellSlope_potentialShellIndexSigma_Ioi
        M n h q (originCube d (K : ℤ)) R hh)
      (fun i j ↦ integrable_weight_mul_pair_of_memLp_two_four M
        (oneStepLowerSourceCellWeight M n h R)
        (oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R · hh)
        (memLp_two_oneStepLowerSourceCellWeight M n h R hh)
        (fun k ↦ memLp_four_oneStepNeumannCellSlope_coord M n h q
          (originCube d (K : ℤ)) R hh hq k) i j)]
  rw [abarStarInv_cube_eq_annealedDualScalar_smul_one M n R
    (oneStepSourceCells_scale_nonneg hsource hR)]
  rw [oneStepSourceCells_scale_toNat_eq hsource hR]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    ite_mul, mul_one, mul_zero, zero_mul, Fintype.sum_ite_eq]
  rw [← Finset.mul_sum]
  congr 1
  change (∑ i : Fin d,
      ∫ omega, oneStepLowerSourceCellWeight M n h R omega *
        (oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh i *
        oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh i) ∂M.P.toMeasure) = _
  unfold vecNormSq vecDot
  have hfun :
      (fun omega ↦
        oneStepLowerSourceCellWeight M n h R omega *
          ∑ i : Fin d,
            oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh i *
              oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh i) =
        fun omega ↦ ∑ i : Fin d,
          oneStepLowerSourceCellWeight M n h R omega *
            (oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh i *
              oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh i) := by
    funext omega
    rw [Finset.mul_sum]
  rw [hfun]
  rw [integral_finset_sum]
  intro i _hi
  exact integrable_weight_mul_pair_of_memLp_two_four M
    (oneStepLowerSourceCellWeight M n h R)
    (oneStepNeumannCellSlope M n h q
      (originCube d (K : ℤ)) R · hh)
    (memLp_two_oneStepLowerSourceCellWeight M n h R hh)
    (fun k ↦ memLp_four_oneStepNeumannCellSlope_coord M n h q
      (originCube d (K : ℤ)) R hh hq k) i i

/-- Normalized finite-family form of the dual inverse-star factorization. -/
theorem normalized_sum_integral_lowerWeight_mul_neumannSourceCellSlope_randomAStarInv_eq
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega,
            oneStepLowerSourceCellWeight M n h R omega *
              vecDot (oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh)
                (matVecMul ((randomAStarMatrix M n
                  (Ch02.cubeDomain R) omega)⁻¹)
                  (oneStepNeumannCellSlope M n h q
                    (originCube d (K : ℤ)) R omega hh))
            ∂M.P.toMeasure =
      oneStepAnnealedDualReadout M n (oneStepLocalizationScale n M.delta) *
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega,
              oneStepLowerSourceCellWeight M n h R omega *
                vecNormSq (oneStepNeumannCellSlope M n h q
                  (originCube d (K : ℤ)) R omega hh)
              ∂M.P.toMeasure) := by
  rw [Finset.sum_congr rfl (fun R hR ↦
    integral_lowerWeight_mul_neumannSourceCellSlope_randomAStarInv_eq
      M n h q R hsource hR hh hq)]
  rw [← Finset.mul_sum]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
