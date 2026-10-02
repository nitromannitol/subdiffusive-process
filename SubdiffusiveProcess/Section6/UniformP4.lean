import SubdiffusiveProcess.Section6.CutoffUniformMoments
import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.AnnealedContrastDecay

/-! Quantitative bounds on the initial P4 contrast, uniform in the shell law. -/
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab hiding TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

noncomputable section
namespace SubdiffusiveProcess.Section6

variable {d : ℕ} [NeZero d]

/-- Uniform bound on an upper ellipticity power moment of the literal cutoff law. -/
theorem integral_Lambda_pow_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : ℕ) (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) {xi : ℕ} (hxi : 0 < xi) :
    (∫ a, (Ch04.LambdaSqCoeffField Q s (.finite 1) a) ^ xi
      ∂aCutoffRestrictionLaw M L) ≤
      (4 * (d : ℝ)) ^ xi * cutoffEnvelopeExpMomentBound d L
        (aCutoffCubeOriginCoverScale Q) M.delta (3 * xi) := by
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  have htarget := (hP.aemeasurable_LambdaSqCoeffField_finite_one Q hs).pow_const xi
  rw [aCutoffRestrictionLaw_eq_map,
    integral_map (measurable_aCutoffRegCoeffField M L).aemeasurable
      htarget.aestronglyMeasurable]
  have hq : 0 < (3 * xi : ℝ) := by positivity
  have hdom := (integrable_exp_mul_aCutoffCubeLogEnvelope M L
    (aCutoffCubeOriginCoverScale Q) hq).const_mul ((4 * (d : ℝ)) ^ xi)
  have hmono := integral_mono
    ((integrable_LambdaSqCoeffField_pow_aCutoffRestrictionLaw M L Q hs xi hxi).comp_aemeasurable
      (measurable_aCutoffRegCoeffField M L).aemeasurable)
    hdom (fun omega => ?_)
  · refine hmono.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_exp_mul_cutoffEnvelope_le M L
      (aCutoffCubeOriginCoverScale Q) hq) (by positivity)
  · have hpw := pow_le_pow_left₀
      (Ch04.LambdaSqCoeffField_finite_nonneg Q (aCutoffRegCoeffField M L omega)
        hs (by norm_num))
      (LambdaSqCoeffField_le_aCutoffCubeLogEnvelope M L omega Q hs) xi
    rw [mul_pow, ← Real.exp_nat_mul] at hpw
    convert hpw using 1
    congr 2
    ring

/-- Uniform bound on an inverse lower ellipticity power moment of the literal cutoff law. -/
theorem integral_lambda_inv_pow_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : ℕ) (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) {xi : ℕ} (hxi : 0 < xi) :
    (∫ a, ((Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹) ^ xi
      ∂aCutoffRestrictionLaw M L) ≤
      (4 * (d : ℝ)) ^ xi * cutoffEnvelopeExpMomentBound d L
        (aCutoffCubeOriginCoverScale Q) M.delta (xi : ℝ) := by
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  have htarget := (hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs).pow_const xi
  rw [aCutoffRestrictionLaw_eq_map,
    integral_map (measurable_aCutoffRegCoeffField M L).aemeasurable
      htarget.aestronglyMeasurable]
  have hq : 0 < (xi : ℝ) := by positivity
  have hdom := (integrable_exp_mul_aCutoffCubeLogEnvelope M L
    (aCutoffCubeOriginCoverScale Q) hq).const_mul ((4 * (d : ℝ)) ^ xi)
  have hmono := integral_mono
    ((integrable_lambdaSqCoeffField_inv_pow_aCutoffRestrictionLaw M L Q hs xi hxi).comp_aemeasurable
      (measurable_aCutoffRegCoeffField M L).aemeasurable)
    hdom (fun omega => ?_)
  · refine hmono.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_exp_mul_cutoffEnvelope_le M L
      (aCutoffCubeOriginCoverScale Q) hq) (by positivity)
  · have hpw := pow_le_pow_left₀
      (inv_nonneg.mpr (Ch04.lambdaSqCoeffField_finite_nonneg Q (aCutoffRegCoeffField M L omega)
        hs (by norm_num)))
      (lambdaSqCoeffField_inv_le_aCutoffCubeLogEnvelope M L omega Q hs) xi
    rw [mul_pow, ← Real.exp_nat_mul] at hpw
    exact hpw

theorem integral_normalized_Lambda_pow_eq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k xi : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ a, (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a) ^ xi
      ∂Ch04.restrictionScaleNormalizedLaw k (aCutoffRestrictionLaw M L)) =
    ∫ a, (Ch04.LambdaSqCoeffField (originCube d (k : ℤ)) s (.finite 1) a) ^ xi
      ∂aCutoffRestrictionLaw M L := by
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  rw [Ch04.integral_restrictionScaleNormalizedLaw k _
    (((hP.scaleNormalized k).aemeasurable_LambdaSqCoeffField_finite_one
      (originCube d 0) hs).pow_const xi).aestronglyMeasurable,
    ← Ch04.rescaleReg_eq_dilateReg_neg_nat k]
  apply integral_congr_ae
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  have hscale := Ch04.LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    ha k 0 s (.finite 1)
  simpa only [Nat.add_zero] using congrArg (fun x : ℝ => x ^ xi) hscale

theorem integral_normalized_lambda_inv_pow_eq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k xi : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ a, ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a)⁻¹) ^ xi
      ∂Ch04.restrictionScaleNormalizedLaw k (aCutoffRestrictionLaw M L)) =
    ∫ a, ((Ch04.lambdaSqCoeffField (originCube d (k : ℤ)) s (.finite 1) a)⁻¹) ^ xi
      ∂aCutoffRestrictionLaw M L := by
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  rw [Ch04.integral_restrictionScaleNormalizedLaw k _
    (((hP.scaleNormalized k).aemeasurable_lambdaSqCoeffField_finite_one_inv
      (originCube d 0) hs).pow_const xi).aestronglyMeasurable,
    ← Ch04.rescaleReg_eq_dilateReg_neg_nat k]
  apply integral_congr_ae
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  have hscale := Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    ha k 0 s (.finite 1)
  simpa only [Nat.add_zero] using congrArg (fun x : ℝ => (x⁻¹) ^ xi) hscale

/-- A common bound on the initial high-moment contrast at fixed cutoff. -/
theorem exists_uniform_initial_contrast_bound (L : ℕ) (delta : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta = delta →
      Ch05.widetildeThetaAtScale (normalizedCutoffLaw M L) 0
        (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L) ≤ B := by
  let k := aCutoffNormalizationDepth d L
  let Q := originCube d (k : ℤ)
  let xi := 8 * d + 1
  let U := (4 * (d : ℝ)) ^ xi * cutoffEnvelopeExpMomentBound d L
    (aCutoffCubeOriginCoverScale Q) delta (3 * xi)
  let V := (4 * (d : ℝ)) ^ xi * cutoffEnvelopeExpMomentBound d L
    (aCutoffCubeOriginCoverScale Q) delta xi
  have hU : 0 ≤ U := mul_nonneg (by positivity)
    (cutoffEnvelopeExpMomentBound_pos _ _ _ _ _).le
  have hV : 0 ≤ V := mul_nonneg (by positivity)
    (cutoffEnvelopeExpMomentBound_pos _ _ _ _ _).le
  refine ⟨U ^ (1 / (xi : ℝ)) * V ^ (1 / (xi : ℝ)),
    mul_nonneg (Real.rpow_nonneg hU _) (Real.rpow_nonneg hV _), ?_⟩
  intro M hdelta
  change Ch04.LambdaMomentAtScale (normalizedCutoffLaw M L) 0 (1 / 4) xi *
    Ch04.lambdaInvMomentAtScale (normalizedCutoffLaw M L) 0 (1 / 4) xi ≤ _
  have hupper := integral_Lambda_pow_le M L Q (s := 1 / 4) (by norm_num)
    (show 0 < xi by dsimp [xi]; omega)
  have hlower := integral_lambda_inv_pow_le M L Q (s := 1 / 4) (by norm_num)
    (show 0 < xi by dsimp [xi]; omega)
  rw [hdelta] at hupper hlower
  unfold Ch04.LambdaMomentAtScale Ch04.lambdaInvMomentAtScale Ch04.annealedMomentRoot
  change (_ : ℝ) ^ (1 / (xi : ℝ)) * (_ : ℝ) ^ (1 / (xi : ℝ)) ≤ _
  rw [show normalizedCutoffLaw M L =
    Ch04.restrictionScaleNormalizedLaw k (aCutoffRestrictionLaw M L) from rfl,
    integral_normalized_Lambda_pow_eq M L k xi (by norm_num),
    integral_normalized_lambda_inv_pow_eq M L k xi (by norm_num)]
  have hupper0 : 0 ≤ ∫ a, (Ch04.LambdaSqCoeffField Q (1 / 4) (.finite 1) a) ^ xi
      ∂aCutoffRestrictionLaw M L :=
    integral_nonneg fun a => pow_nonneg
      (Ch04.LambdaSqCoeffField_finite_nonneg Q a (by norm_num) (by norm_num)) _
  have hlower0 : 0 ≤ ∫ a, ((Ch04.lambdaSqCoeffField Q (1 / 4) (.finite 1) a)⁻¹) ^ xi
      ∂aCutoffRestrictionLaw M L :=
    integral_nonneg fun a => pow_nonneg (inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg Q a (by norm_num) (by norm_num))) _
  exact mul_le_mul (Real.rpow_le_rpow hupper0 hupper (by positivity))
    (Real.rpow_le_rpow hlower0 hlower (by positivity))
    (Real.rpow_nonneg hlower0 _) (Real.rpow_nonneg hU _)

end SubdiffusiveProcess.Section6
