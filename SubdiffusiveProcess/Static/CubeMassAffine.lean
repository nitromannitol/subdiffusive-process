module

public import SubdiffusiveProcess.Static.SignedCubeMoments
public import SubdiffusiveProcess.Static.AffineIntegrals
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

@[expose] public section

/-! # Exact cube mass in the locally dilated coordinates -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open Homogenization hiding Vec TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Every origin cube is the sup-norm ball of its exact side. -/
theorem originCube_eq_ball (d : ℕ) (k : ℤ) :
    openCubeSet (originCube d k) = Metric.ball (0 : Vec d) ((3 : ℝ) ^ k / 2) := by
  have hcenter : Homogenization.cubeCenter (originCube d k) = 0 := by
    funext i
    simp [Homogenization.cubeCenter, Homogenization.cubeScaleFactor, originCube]
  have h := (ball_cubeCenter_eq_openCubeSet (originCube d k)).symm
  rw [hcenter] at h
  simpa [Homogenization.cubeRadius, Homogenization.cubeScaleFactor, originCube, div_eq_mul_inv, mul_comm] using h

/-- A continuous nonnegative function has exactly volume times its cube mean. -/
theorem lintegral_cube_eq_volume_mul_average {d : ℕ} (Q : Homogenization.TriadicCube d)
    (f : Vec d → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫⁻ x in openCubeSet Q, ENNReal.ofReal (f x)) =
      ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal (cubeAverage Q f) := by
  have hint : IntegrableOn f (openCubeSet Q) :=
    (hf.continuousOn.integrableOn_compact
      (ProperSpace.isCompact_closedBall (cubeCenter Q) (cubeRadius Q))).mono_set
        ((openCubeSet_subset_cubeSet Q).trans (cubeSet_subset_closedBall Q))
  rw [← ENNReal.ofReal_mul (cubeVolume_nonneg Q)]
  have havg : cubeVolume Q * cubeAverage Q f = ∫ x in openCubeSet Q, f x := by
    unfold cubeAverage
    rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    field_simp [(cubeVolume_pos Q).ne']
  rw [havg]
  exact (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0)).symm

/-- The normalized physical translated mean is its unit-chart lower integral. -/
theorem translatedCutoffAverage_unit_integral {d : ℕ} (M : GMCModel d)
    (j : ℕ) (k : ℤ) (c : Vec d) (ω : PotentialSample d) :
    (∫⁻ x in openCubeSet (originCube d 0),
      ENNReal.ofReal (aCutoff M j ω (c + (3 : ℝ) ^ k • x))) =
        ENNReal.ofReal (translatedCutoffAverage M j k c ω) := by
  let f := aCutoff M j (translatePotentialSample c ω)
  have hmass := lintegral_cube_eq_volume_mul_average (originCube d k) f
    (continuous_aCutoff M j _) (fun x => (aCutoff_pos M j _ x).le)
  have hchart := lintegral_ball_affine (0 : Vec d)
    (zpow_pos (by norm_num : (0 : ℝ) < 3) k) (fun x => ENNReal.ofReal (f x))
  rw [← originCube_eq_ball d k] at hchart
  have hfun : (fun x => ENNReal.ofReal (f (0 + (3 : ℝ) ^ k • x))) =
      fun x => ENNReal.ofReal (aCutoff M j ω (c + (3 : ℝ) ^ k • x)) := by
    funext x
    dsimp only [f]
    rw [zero_add, Section6Covariance.aCutoff_translatePotentialSample, add_comm]
  rw [hfun] at hchart
  have hvol : cubeVolume (originCube d k) = ((3 : ℝ) ^ k) ^ d := by
    simp [cubeVolume, cubeScaleFactor, originCube]
  rw [hvol] at hmass
  have heq : ENNReal.ofReal (((3 : ℝ) ^ k) ^ d) *
      (∫⁻ x in openCubeSet (originCube d 0),
        ENNReal.ofReal (aCutoff M j ω (c + (3 : ℝ) ^ k • x))) =
      ENNReal.ofReal (((3 : ℝ) ^ k) ^ d) *
        ENNReal.ofReal (translatedCutoffAverage M j k c ω) := hchart.symm.trans hmass
  exact (ENNReal.mul_right_inj (by positivity) ENNReal.ofReal_ne_top).mp heq

/-- The dilated finite prefix has the exact mesh-cube mass at every signed scale. -/
theorem lintegral_scaled_cutoff_ball {d : ℕ} (M : GMCModel d) (j m n t : ℕ)
    (z c : Vec d) (ω : PotentialSample d) :
    (∫⁻ x in Metric.ball c ((3 : ℝ) ^ ((t : ℤ) - n) / 2),
      ENNReal.ofReal (aCutoff M j ω (z + (3 : ℝ) ^ m • x))) =
        ENNReal.ofReal (((3 : ℝ) ^ ((t : ℤ) - n)) ^ d) *
          ENNReal.ofReal (translatedCutoffAverage M j ((m : ℤ) - n + t)
            (z + (3 : ℝ) ^ m • c) ω) := by
  rw [lintegral_ball_affine c (zpow_pos (by norm_num : (0 : ℝ) < 3) _)]
  congr 1
  have hscale : (3 : ℝ) ^ m * (3 : ℝ) ^ ((t : ℤ) - n) =
      (3 : ℝ) ^ ((m : ℤ) - n + t) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have hfun : (fun x : Vec d => ENNReal.ofReal
      (aCutoff M j ω (z + (3 : ℝ) ^ m • (c + (3 : ℝ) ^ ((t : ℤ) - n) • x)))) =
      fun x => ENNReal.ofReal (aCutoff M j ω
        ((z + (3 : ℝ) ^ m • c) + (3 : ℝ) ^ ((m : ℤ) - n + t) • x)) := by
    funext x
    rw [smul_add, smul_smul, hscale, add_assoc]
  rw [hfun, translatedCutoffAverage_unit_integral]

end SubdiffusiveProcess.Static
