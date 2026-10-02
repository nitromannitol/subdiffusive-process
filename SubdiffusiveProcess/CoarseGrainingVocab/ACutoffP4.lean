import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffNormalization
import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4Bounds
import Homogenization.Book.Ch05.Definitions

/-!
# Quantitative coarse-grained ellipticity for the normalized GMC cutoff law

This module transports the samplewise lognormal bounds through the literal
cutoff pushforward and then through the canonical range normalization.

PROVENANCE: follows, in order,
`Algsuperdiff/Section3/Cutoff/P4.lean`, `P4UpperLaw.lean`, and
`NormalizedP4.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Set Homogenization Homogenization.Book

noncomputable section


private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Dimension-only parameters used for the GMC `(P4)` record. -/
def aCutoffP4Params (d : ℕ) (hd : 2 ≤ d) :
    Ch05.QuantitativeCoarseGrainedEllipticityParams d where
  sUpper := (1 : ℝ) / 4
  sLower := (1 : ℝ) / 4
  xi := 8 * d + 1
  two_le_dim := hd
  sUpper_nonneg := by norm_num
  sUpper_lt_one := by norm_num
  sLower_nonneg := by norm_num
  sLower_lt_one := by norm_num
  xi_gt_two_mul_dim := by
    norm_num
    exact_mod_cast (show 2 * d < 8 * d + 1 by omega)
  sum_lt_one := by norm_num
  dim_div_xi_lt_min := by
    rw [min_eq_left]
    · have hxi : (0 : ℝ) < (8 * d + 1 : ℕ) := by positivity
      rw [div_lt_iff₀ hxi]
      norm_num
      have hreal : ((4 * d : ℕ) : ℝ) < ((8 * d + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 4 * d < 8 * d + 1 by omega)
      push_cast at hreal
      nlinarith
    · norm_num

@[simp] theorem aCutoffP4Params_sUpper (d : ℕ) (hd : 2 ≤ d) :
    (aCutoffP4Params d hd).sUpper = (1 : ℝ) / 4 := rfl

@[simp] theorem aCutoffP4Params_sLower (d : ℕ) (hd : 2 ≤ d) :
    (aCutoffP4Params d hd).sLower = (1 : ℝ) / 4 := rfl

variable {d : ℕ} [NeZero d]

theorem integrable_LambdaSqCoeffField_pow_aCutoffRestrictionLaw
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (xi : ℕ) (hxi : 0 < xi) :
    Integrable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField Q s (.finite 1) a) ^ xi)
      (aCutoffRestrictionLaw M L) := by
  let P := aCutoffRestrictionLaw M L
  let f : Sample d → RegCoeffField d := aCutoffRegCoeffField M L
  let C : ℝ := 4 * (d : ℝ)
  let Z : Sample d → ℝ := fun omega =>
    aCutoffCubeLogEnvelope M L (aCutoffCubeOriginCoverScale Q) omega
  let hP : Ch04.RestrictionLawCarrier P := aCutoffRestrictionLaw_lawCarrier M L
  have htarget : AEMeasurable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField Q s (.finite 1) a) ^ xi) P :=
    (hP.aemeasurable_LambdaSqCoeffField_finite_one Q hs).pow_const xi
  have hq : 0 < (3 * xi : ℝ) := by positivity
  have hExp : Integrable (fun omega : Sample d => Real.exp ((3 * xi : ℝ) * Z omega))
      M.P.toMeasure := by
    simpa [Z] using integrable_exp_mul_aCutoffCubeLogEnvelope M L
      (aCutoffCubeOriginCoverScale Q) hq
  have hdom : Integrable (fun omega : Sample d =>
      C ^ xi * Real.exp ((3 * xi : ℝ) * Z omega)) M.P.toMeasure :=
    hExp.const_mul _
  change Integrable _ P
  rw [show P = Measure.map f M.P.toMeasure by
    simp [P, f, aCutoffRestrictionLaw_eq_map]]
  apply (integrable_map_measure htarget.aestronglyMeasurable
    (measurable_aCutoffRegCoeffField M L).aemeasurable).mpr
  refine Integrable.mono' hdom
    (htarget.comp_aemeasurable
      (measurable_aCutoffRegCoeffField M L).aemeasurable).aestronglyMeasurable ?_
  filter_upwards with omega
  have hbase0 : 0 ≤ Ch04.LambdaSqCoeffField Q s (.finite 1) (f omega) :=
    Ch04.LambdaSqCoeffField_finite_nonneg Q (f omega) hs (by norm_num)
  have hbound : Ch04.LambdaSqCoeffField Q s (.finite 1) (f omega) ≤
      C * Real.exp (3 * Z omega) := by
    simpa [C, Z, f] using
      LambdaSqCoeffField_le_aCutoffCubeLogEnvelope M L omega Q hs
  have hpw := pow_le_pow_left₀ hbase0 hbound xi
  have heq : (C * Real.exp (3 * Z omega)) ^ xi =
      C ^ xi * Real.exp ((3 * xi : ℝ) * Z omega) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  simpa only [f, Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hbase0 xi),
    abs_of_nonneg (by positivity : 0 ≤ C ^ xi * Real.exp ((3 * xi : ℝ) * Z omega)),
    heq] using hpw

theorem integrable_lambdaSqCoeffField_inv_pow_aCutoffRestrictionLaw
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (xi : ℕ) (hxi : 0 < xi) :
    Integrable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹) ^ xi)
      (aCutoffRestrictionLaw M L) := by
  let P := aCutoffRestrictionLaw M L
  let f : Sample d → RegCoeffField d := aCutoffRegCoeffField M L
  let C : ℝ := 4 * (d : ℝ)
  let Z : Sample d → ℝ := fun omega =>
    aCutoffCubeLogEnvelope M L (aCutoffCubeOriginCoverScale Q) omega
  let hP : Ch04.RestrictionLawCarrier P := aCutoffRestrictionLaw_lawCarrier M L
  have htarget : AEMeasurable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹) ^ xi) P :=
    (hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs).pow_const xi
  have hq : 0 < (xi : ℝ) := by exact_mod_cast hxi
  have hExp : Integrable (fun omega : Sample d => Real.exp ((xi : ℝ) * Z omega))
      M.P.toMeasure := by
    simpa [Z] using integrable_exp_mul_aCutoffCubeLogEnvelope M L
      (aCutoffCubeOriginCoverScale Q) hq
  have hdom : Integrable (fun omega : Sample d =>
      C ^ xi * Real.exp ((xi : ℝ) * Z omega)) M.P.toMeasure := hExp.const_mul _
  change Integrable _ P
  rw [show P = Measure.map f M.P.toMeasure by
    simp [P, f, aCutoffRestrictionLaw_eq_map]]
  apply (integrable_map_measure htarget.aestronglyMeasurable
    (measurable_aCutoffRegCoeffField M L).aemeasurable).mpr
  refine Integrable.mono' hdom
    (htarget.comp_aemeasurable
      (measurable_aCutoffRegCoeffField M L).aemeasurable).aestronglyMeasurable ?_
  filter_upwards with omega
  have hbase0 : 0 ≤
      (Ch04.lambdaSqCoeffField Q s (.finite 1) (f omega))⁻¹ :=
    inv_nonneg.mpr (Ch04.lambdaSqCoeffField_finite_nonneg Q (f omega) hs (by norm_num))
  have hbound : (Ch04.lambdaSqCoeffField Q s (.finite 1) (f omega))⁻¹ ≤
      C * Real.exp (Z omega) := by
    simpa [C, Z, f] using
      lambdaSqCoeffField_inv_le_aCutoffCubeLogEnvelope M L omega Q hs
  have hpw := pow_le_pow_left₀ hbase0 hbound xi
  have heq : (C * Real.exp (Z omega)) ^ xi =
      C ^ xi * Real.exp ((xi : ℝ) * Z omega) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  simpa only [f, Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hbase0 xi),
    abs_of_nonneg (by positivity : 0 ≤ C ^ xi * Real.exp ((xi : ℝ) * Z omega)),
    heq] using hpw

private theorem integrable_normalized_LambdaSq_pow
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k xi : ℕ)
    {s : ℝ} (hs : 0 < s) (hxi : 0 < xi) :
    Integrable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a) ^ xi)
      (Ch04.restrictionScaleNormalizedLaw k (aCutoffRestrictionLaw M L)) := by
  let P := aCutoffRestrictionLaw M L
  let hP : Ch04.RestrictionLawCarrier P := aCutoffRestrictionLaw_lawCarrier M L
  let hnorm := hP.scaleNormalized k
  have htarget : AEStronglyMeasurable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a) ^ xi)
      (Ch04.restrictionScaleNormalizedLaw k P) :=
    ((hnorm.aemeasurable_LambdaSqCoeffField_finite_one
      (originCube d (0 : ℤ)) hs).pow_const xi).aestronglyMeasurable
  apply (Ch04.integrable_restrictionScaleNormalizedLaw_iff k htarget).mpr
  rw [← Ch04.rescaleReg_eq_dilateReg_neg_nat k]
  refine (integrable_LambdaSqCoeffField_pow_aCutoffRestrictionLaw M L
    (originCube d (k : ℤ)) hs xi hxi).congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  have hscale :=
    Ch04.LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k 0 s (.finite 1)
  simpa only [Nat.add_zero] using congrArg (fun x : ℝ => x ^ xi) hscale.symm

private theorem integrable_normalized_lambdaSq_inv_pow
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k xi : ℕ)
    {s : ℝ} (hs : 0 < s) (hxi : 0 < xi) :
    Integrable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a)⁻¹) ^ xi)
      (Ch04.restrictionScaleNormalizedLaw k (aCutoffRestrictionLaw M L)) := by
  let P := aCutoffRestrictionLaw M L
  let hP : Ch04.RestrictionLawCarrier P := aCutoffRestrictionLaw_lawCarrier M L
  let hnorm := hP.scaleNormalized k
  have htarget : AEStronglyMeasurable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a)⁻¹) ^ xi)
      (Ch04.restrictionScaleNormalizedLaw k P) :=
    ((hnorm.aemeasurable_lambdaSqCoeffField_finite_one_inv
      (originCube d (0 : ℤ)) hs).pow_const xi).aestronglyMeasurable
  apply (Ch04.integrable_restrictionScaleNormalizedLaw_iff k htarget).mpr
  rw [← Ch04.rescaleReg_eq_dilateReg_neg_nat k]
  refine (integrable_lambdaSqCoeffField_inv_pow_aCutoffRestrictionLaw M L
    (originCube d (k : ℤ)) hs xi hxi).congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  have hscale :=
    Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k 0 s (.finite 1)
  simpa only [Nat.add_zero] using congrArg (fun x : ℝ => (x⁻¹) ^ xi) hscale.symm

end

noncomputable section

variable {d : ℕ}

/-- Exact `(P4)` evidence for the canonically normalized GMC cutoff law. -/
noncomputable def aCutoffNormalization_quantitativeCoarseGrainedEllipticity
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    @Ch05.QuantitativeCoarseGrainedEllipticity d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
      (Ch04.restrictionScaleNormalizedLaw (aCutoffNormalizationDepth d L)
        (aCutoffRestrictionLaw M L)) := by
  letI : NeZero d := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let params := aCutoffP4Params d M.shellPrefix.dimension
  refine {
    sUpper := params.sUpper
    sLower := params.sLower
    xi := params.xi
    two_le_dim := params.two_le_dim
    sUpper_nonneg := params.sUpper_nonneg
    sUpper_lt_one := params.sUpper_lt_one
    sLower_nonneg := params.sLower_nonneg
    sLower_lt_one := params.sLower_lt_one
    xi_gt_two_mul_dim := params.xi_gt_two_mul_dim
    sum_lt_one := params.sum_lt_one
    dim_div_xi_lt_min := params.dim_div_xi_lt_min
    upper_moment_integrable := ?_
    lower_inv_moment_integrable := ?_ }
  · simpa only [params, aCutoffP4Params_sUpper] using
      integrable_normalized_LambdaSq_pow M L (aCutoffNormalizationDepth d L)
        params.xi (by norm_num) (by simp [params, aCutoffP4Params])
  · simpa only [params, aCutoffP4Params_sLower] using
      integrable_normalized_lambdaSq_inv_pow M L (aCutoffNormalizationDepth d L)
        params.xi (by norm_num) (by simp [params, aCutoffP4Params])

end

end SubdiffusiveProcess.CoarseGrainingVocab
