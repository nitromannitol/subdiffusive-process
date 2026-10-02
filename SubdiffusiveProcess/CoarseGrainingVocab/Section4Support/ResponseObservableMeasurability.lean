import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpTwoBlockMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitResponseMoment

/-!
# Section 4 support: response-observable measurability

The positive- and subunit-scale payloads are literal countable suprema of
responses normalized by a random spatial average.  This module proves their
measurability through the already-landed random primal and dual coarse
matrices.  No new variational measurability argument is introduced.

This is the GMC analogue of the measurable representative layer in
`Algsuperdiff/Section3/Observable/CutoffResponseJCommonRepresentative.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The normalized tail-coefficient cube average is measurable in the cutoff
sample. -/
theorem measurable_tailCoefficientCubeAverage {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    Measurable (tailCoefficientCubeAverage M L m) := by
  let U : Set (Vec d) := openCubeSet (originCube d (m : ℤ))
  have hJoint : Measurable (fun z : Sample d × Vec d =>
      tailCoefficient M L m z.1 z.2) := by
    unfold tailCoefficient
    exact measurable_const.mul
      ((measurable_cutoff_uncurry M L).div
        (measurable_cutoff_uncurry M (min m L)))
  have hInt : Measurable (fun omega : Sample d =>
      ∫ x, tailCoefficient M L m omega x ∂(volume.restrict U)) :=
    hJoint.stronglyMeasurable.integral_prod_right'.measurable
  unfold tailCoefficientCubeAverage Ch02.average
  exact measurable_const.mul hInt

/-- Coarse response matrix when the scalar normalization is itself random. -/
noncomputable def randomNormalizedResponseMatrix {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (b : Sample d → ℝ) (omega : Sample d) : Mat d :=
  let c := Real.sqrt (b omega)
  ((1 / 2 : ℝ) * (c⁻¹) ^ 2) • randomAMatrix M L U omega +
    ((1 / 2 : ℝ) * c ^ 2) • randomSigmaStarInvMatrix M L U omega -
      (c⁻¹ * c) • (1 : Mat d)

theorem measurable_randomNormalizedResponseMatrix {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    {b : Sample d → ℝ} (hb : Measurable b) :
    Measurable (randomNormalizedResponseMatrix M L U b) := by
  have hB : Measurable (randomSigmaStarInvMatrix M L U) :=
    (measurable_randomSigmaStarInvMatrix_potentialShellIndexSigma_Iic M L U).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [randomNormalizedResponseMatrix, Matrix.add_apply,
    Matrix.sub_apply]
  have hc : Measurable (fun omega => Real.sqrt (b omega)) :=
    hb.sqrt
  exact ((measurable_const.mul (hc.inv.pow_const 2)).mul
      ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp (measurable_randomAMatrix M L U)))).add
    ((measurable_const.mul (hc.pow_const 2)).mul
      ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp hB))) |>.sub
          ((hc.inv.mul hc).mul measurable_const)

/-- Identification of the random-normalization response with the quadratic
form of `randomNormalizedResponseMatrix`. -/
theorem randomNormalizedResponseMatrix_quadratic {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (b : Sample d → ℝ) (omega : Sample d) (e : Vec d) :
    J U (aCutoffCoeffOnData M L omega U).toCoeffOn
        ((Real.sqrt (b omega))⁻¹ • e) (Real.sqrt (b omega) • e) =
      vecDot e
        (matVecMul (randomNormalizedResponseMatrix M L U b omega) e) := by
  let c := Real.sqrt (b omega)
  let hdata := aCutoffCoeffOnData M L omega U
  let a := hdata.toCoeffOn
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U a hdata.isSymmetric
  have hsplit := hTheory.response_dirichlet_neumann_split (c⁻¹ • e) (c • e)
  rw [hTheory.dirichlet_value_by_sigma, hTheory.neumann_value_by_sigmaStarInv]
    at hsplit
  have hsplit' : J U a (c⁻¹ • e) (c • e) =
      (1 / 2 : ℝ) * vecDot (c⁻¹ • e)
          (matVecMul (Ch02.sigmaCoarse U a) (c⁻¹ • e)) +
        (1 / 2 : ℝ) * vecDot (c • e)
          (matVecMul (Ch02.sigmaStarInvCoarse U a) (c • e)) -
        vecDot (c⁻¹ • e) (c • e) := hsplit
  change J U a (c⁻¹ • e) (c • e) = _
  rw [hsplit']
  change _ = vecDot e
    (matVecMul
      (((1 / 2 : ℝ) * (c⁻¹) ^ 2) • Ch02.aCoarse U a +
        ((1 / 2 : ℝ) * c ^ 2) • Ch02.sigmaStarInvCoarse U a -
          (c⁻¹ * c) • (1 : Mat d)) e)
  rw [hTheory.derived_matrices.1]
  have vecDot_sub (x y z : Vec d) :
      vecDot x (y - z) = vecDot x y - vecDot x z := by
    simp [vecDot, Finset.sum_sub_distrib, mul_sub]
  simp only [add_matVecMul, sub_matVecMul, smul_matVecMul,
    vecDot_add_right, vecDot_sub, vecDot_smul_right,
    matVecMul_smul, vecDot_smul_left]
  have hone : matVecMul (1 : Mat d) e = e := Matrix.one_mulVec e
  rw [hone]
  ring

theorem randomNormalizedResponseMatrix_posSemidef {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (b : Sample d → ℝ) (omega : Sample d) :
    (randomNormalizedResponseMatrix M L U b omega).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hA : (randomAMatrix M L U omega).IsSymm := by
      let hdata := aCutoffCoeffOnData M L omega U
      have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U
        hdata.toCoeffOn hdata.isSymmetric
      change (Ch02.aCoarse U hdata.toCoeffOn).IsSymm
      rw [hTheory.derived_matrices.1]
      exact Ch02.sigmaCoarse_isSymm U hdata.toCoeffOn
    have hB : (randomSigmaStarInvMatrix M L U omega).IsSymm :=
      Ch02.sigmaStarInvCoarse_isSymm U
        (aCutoffCoeffOnData M L omega U).toCoeffOn
    let c := Real.sqrt (b omega)
    have hsymm := ((hA.smul ((1 / 2 : ℝ) * (c⁻¹) ^ 2)).add
      (hB.smul ((1 / 2 : ℝ) * c ^ 2))).sub
        (Matrix.isSymm_one.smul (c⁻¹ * c))
    simpa [Matrix.IsHermitian, Matrix.IsSymm,
      randomNormalizedResponseMatrix, c] using hsymm
  · intro e
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      (show 0 ≤ J U (aCutoffCoeffOnData M L omega U).toCoeffOn
          ((Real.sqrt (b omega))⁻¹ • e) (Real.sqrt (b omega) • e) from
        Ch02.responseJ_nonneg U _ _ _).trans_eq
          (randomNormalizedResponseMatrix_quadratic M L U b omega e)

/-- A cutoff response normalized by a positive measurable random scalar has a
measurable literal unit-sphere maximum. -/
theorem measurable_paperScalarProbeMaxOn_cutoff_randomNormalization
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) {b : Sample d → ℝ} (hb : Measurable b) :
    Measurable (fun omega => paperScalarProbeMaxOn U
      (aCutoffCoeffOnData M L omega U).toCoeffOn (b omega)) := by
  letI : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  let R := randomNormalizedResponseMatrix M L U b
  have hR : Measurable R := measurable_randomNormalizedResponseMatrix M L U hb
  have hEq : (fun omega => paperScalarProbeMaxOn U
      (aCutoffCoeffOnData M L omega U).toCoeffOn (b omega)) =
      fun omega => ENNReal.ofReal (Ch02.matrixOperatorNorm (R omega)) := by
    funext omega
    exact paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm U
      (aCutoffCoeffOnData M L omega U).toCoeffOn (b omega) (R omega)
      (randomNormalizedResponseMatrix_posSemidef M L U b omega)
      (randomNormalizedResponseMatrix_quadratic M L U b omega)
  rw [hEq]
  apply ENNReal.continuous_ofReal.measurable.comp
  rw [show (fun omega => Ch02.matrixOperatorNorm (R omega)) =
      fun omega => ‖R omega‖ by
    funext omega
    exact Ch02.matrixOperatorNorm_eq_l2_opNorm (R omega)]
  exact continuous_norm.measurable.comp hR

theorem measurable_positiveScaleResponseObservable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (Q : TriadicCube d) :
    Measurable (positiveScaleResponseObservable M m Q) := by
  unfold positiveScaleResponseObservable
  exact Measurable.iSup fun L =>
    measurable_paperScalarProbeMaxOn_cutoff_randomNormalization M L.1
      (Ch02.cubeDomain Q) (measurable_tailCoefficientCubeAverage M L.1 m)

theorem measurable_subunitResponseObservable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (k : ℤ) :
    Measurable (subunitResponseObservable M m k) := by
  unfold subunitResponseObservable
  exact Measurable.iSup fun L => Measurable.iSup fun R =>
    measurable_paperScalarProbeMaxOn_cutoff_randomNormalization M L.1
      (Ch02.cubeDomain R.1) (measurable_tailCoefficientCubeAverage M L.1 m)

end

end SubdiffusiveProcess.CoarseGrainingVocab
