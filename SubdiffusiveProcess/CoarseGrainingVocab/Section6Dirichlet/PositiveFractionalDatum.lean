module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DilationWeakEquation
public import Homogenization.Sobolev.Fractional.EuclideanWspDilation
public import Homogenization.Sobolev.Fractional.EuclideanWspLpMembership
public import Homogenization.Sobolev.Fractional.EuclideanWspPowerTwoBridge
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.SeminormComparison
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalScaledDatumEnergy
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

@[expose] public section

/-!
# Positive fractional control of the dilated Dirichlet datum

The vector divergence lift is coordinatewise `H¹` on the unit cube.  This
file first places that field in the exact Euclidean `H^s = W^{s,2}` carrier,
using the field itself as the continuous `K`-functional competitor.  It then
applies the exact triadic dilation law to
`G(y) = alpha * 3^{-m} F(3^{-m} y)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The normalized Euclidean `L²` realization of a coordinatewise `H¹`
vector field on the centered unit cube. -/
noncomputable def unitEuclideanL2FieldOfCubeVectorH1
    {d : ℕ} (F : CubeVectorH1Function (originCube d 0)) :
    UnitCubeEuclideanL2Field d :=
  { toField := F.toField
    euclideanMemL2 := F.toContinuousKCompetitor.euclideanMemL2 }

@[simp] theorem unitEuclideanL2FieldOfCubeVectorH1_apply
    {d : ℕ} (F : CubeVectorH1Function (originCube d 0)) (x : Vec d) :
    unitEuclideanL2FieldOfCubeVectorH1 F x = F.toField x := rfl

/-- The continuous `K`-functional of an `H¹` field is bounded at scale `t`
by `t` times its coordinate-summed normalized gradient norm. -/
theorem continuousKFunctional_unitEuclideanL2FieldOfCubeVectorH1_le
    {d : ℕ} (F : CubeVectorH1Function (originCube d 0))
    (t : ContinuousKScale) :
    continuousKFunctional t (unitEuclideanL2FieldOfCubeVectorH1 F) ≤
      t.1 * F.gradientCoordL2NormSum := by
  let U : UnitCubeEuclideanL2Field d := unitEuclideanL2FieldOfCubeVectorH1 F
  let G : ContinuousKCompetitor d := F.toContinuousKCompetitor
  have hres : continuousKResidualNorm U G = 0 := by
    unfold continuousKResidualNorm
    change (eLpNorm (fun x => euclideanNorm (U x - G.toField x)) 2
      (unitCenteredCubeDomain d).normalizedVolume).toReal = 0
    have hzero : (fun x => euclideanNorm (U x - G.toField x)) =
        (fun _ : Vec d => 0) := by
      funext x
      have hfield : U x - G.toField x = 0 := by
        ext i
        change (F.coord i).toFun x - (F.coord i).toFun x = 0
        ring
      rw [hfield]
      simp
    rw [hzero]
    simp
  have hgrad : continuousKGradientNorm G ≤ F.gradientCoordL2NormSum := by
    simpa only [G,
      CubeVectorH1Function.toContinuousKCompetitor_toCubeVectorH1Function,
      CubeVectorH1Function.relativeGradientCoordL2NormSum_originCube_zero] using
      continuousKGradientNorm_le_cubeRelativeGradientCoordL2NormSum G
  calc
    continuousKFunctional t U ≤
        continuousKFunctionalCompetitorValue t U G :=
      continuousKFunctional_le_competitor t U G
    _ = t.1 * continuousKGradientNorm G := by
      unfold continuousKFunctionalCompetitorValue
      rw [hres, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, ← mul_pow,
        Real.sqrt_sq_eq_abs,
        abs_mul, abs_of_pos (ContinuousKScale.pos t),
        abs_of_nonneg (continuousKGradientNorm_nonneg G)]
    _ ≤ t.1 * F.gradientCoordL2NormSum :=
      mul_le_mul_of_nonneg_left hgrad (ContinuousKScale.pos t).le

/-- The one-dimensional interpolation integral produced by the linear
competitor `K(t,F) ≤ t ||∇F||`. -/
noncomputable def linearKSeminormIntegral (s : FractionalOrder) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.rpow t (1 - 2 * s.1))

/-- Square-root constant for the linear `K`-functional competitor. -/
noncomputable def linearKSeminormConstant (s : FractionalOrder) : ℝ≥0∞ :=
  (linearKSeminormIntegral s) ^ (1 / 2 : ℝ)

theorem linearKSeminormIntegral_lt_top (s : FractionalOrder) :
    linearKSeminormIntegral s < ∞ := by
  have hint : IntegrableOn (fun t : ℝ => Real.rpow t (1 - 2 * s.1))
      (Set.Ioo (0 : ℝ) 1) := by
    change IntegrableOn (fun t : ℝ => t ^ (1 - 2 * s.1 : ℝ))
      (Set.Ioo (0 : ℝ) 1)
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).2 (by
      linarith [s.2.2])
  simpa only [linearKSeminormIntegral] using hint.lintegral_lt_top

theorem linearKSeminormConstant_lt_top (s : FractionalOrder) :
    linearKSeminormConstant s < ∞ := by
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (linearKSeminormIntegral_lt_top s).ne

/-- The exact continuous interpolation seminorm of a unit-cube `H¹` vector
field is controlled by its coordinate-summed gradient norm. -/
theorem continuousKSeminorm_unitEuclideanL2FieldOfCubeVectorH1_le
    {d : ℕ} (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    continuousKSeminorm s (unitEuclideanL2FieldOfCubeVectorH1 F) ≤
      ENNReal.ofReal F.gradientCoordL2NormSum * linearKSeminormConstant s := by
  let U : UnitCubeEuclideanL2Field d := unitEuclideanL2FieldOfCubeVectorH1 F
  let B : ℝ := F.gradientCoordL2NormSum
  have hB : 0 ≤ B := F.gradientCoordL2NormSum_nonneg
  have hintegrand : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      continuousKSeminormIntegrand s.1 U t ≤
        (ENNReal.ofReal B) ^ 2 *
          ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) := by
    intro t ht
    let kt : ContinuousKScale := ⟨t, ⟨ht.1, ht.2.le⟩⟩
    have hK : continuousKFunctional kt U ≤ t * B := by
      simpa only [U, B] using
        continuousKFunctional_unitEuclideanL2FieldOfCubeVectorH1_le F kt
    have htB : 0 ≤ t * B := mul_nonneg ht.1.le hB
    have hKsq : continuousKFunctional kt U ^ 2 ≤ (t * B) ^ 2 :=
      (sq_le_sq₀ (continuousKFunctional_nonneg kt U) htB).2 hK
    have hpower :
        Real.rpow t (-2 * s.1) * t ^ 2 * t⁻¹ =
          Real.rpow t (1 - 2 * s.1) := by
      have htwo : t ^ (2 : ℕ) = Real.rpow t (2 : ℝ) :=
        (Real.rpow_natCast t 2).symm
      calc
        Real.rpow t (-2 * s.1) * t ^ 2 * t⁻¹ =
            Real.rpow t (-2 * s.1) * Real.rpow t (2 : ℝ) *
              Real.rpow t (-1 : ℝ) := by
                rw [htwo]
                congr 1
                exact (Real.rpow_neg_one t).symm
        _ = Real.rpow t (-2 * s.1 + 2) * Real.rpow t (-1 : ℝ) := by
          exact congrArg (fun z => z * Real.rpow t (-1 : ℝ))
            (Real.rpow_add ht.1 (-2 * s.1) 2).symm
        _ = Real.rpow t ((-2 * s.1 + 2) + (-1)) := by
          exact (Real.rpow_add ht.1 (-2 * s.1 + 2) (-1)).symm
        _ = Real.rpow t (1 - 2 * s.1) := by congr 1; ring
    have hreal :
        Real.rpow t (-2 * s.1) * (t * B) ^ 2 * t⁻¹ =
          B ^ 2 * Real.rpow t (1 - 2 * s.1) := by
      calc
        Real.rpow t (-2 * s.1) * (t * B) ^ 2 * t⁻¹ =
            B ^ 2 * (Real.rpow t (-2 * s.1) * t ^ 2 * t⁻¹) := by ring
        _ = B ^ 2 * Real.rpow t (1 - 2 * s.1) := by rw [hpower]
    rw [continuousKSeminormIntegrand_eq_of_mem s.1 U ht]
    calc
      ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
            ENNReal.ofReal (continuousKFunctional kt U ^ 2) *
            ENNReal.ofReal t⁻¹ ≤
          ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
            ENNReal.ofReal ((t * B) ^ 2) * ENNReal.ofReal t⁻¹ := by
              gcongr
      _ = (ENNReal.ofReal B) ^ 2 *
          ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) := by
        have hlhs :
            ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
                ENNReal.ofReal ((t * B) ^ 2) * ENNReal.ofReal t⁻¹ =
              ENNReal.ofReal
                (Real.rpow t (-2 * s.1) * (t * B) ^ 2 * t⁻¹) := by
          calc
            ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
                  ENNReal.ofReal ((t * B) ^ 2) * ENNReal.ofReal t⁻¹ =
                  ENNReal.ofReal
                    (Real.rpow t (-2 * s.1) * (t * B) ^ 2) *
                  ENNReal.ofReal t⁻¹ := by
                    exact congrArg (fun z => z * ENNReal.ofReal t⁻¹)
                      (ENNReal.ofReal_mul
                        (p := Real.rpow t (-2 * s.1)) (q := (t * B) ^ 2)
                        (Real.rpow_nonneg ht.1.le _)).symm
            _ = ENNReal.ofReal
                (Real.rpow t (-2 * s.1) * (t * B) ^ 2 * t⁻¹) :=
              (ENNReal.ofReal_mul
                (mul_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg (t * B)))).symm
        have hrhs :
            (ENNReal.ofReal B) ^ 2 *
                ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) =
              ENNReal.ofReal (B ^ 2 * Real.rpow t (1 - 2 * s.1)) := by
          rw [ENNReal.ofReal_mul (sq_nonneg B), ENNReal.ofReal_pow hB]
        rw [hlhs, hrhs, hreal]
  have hintegral :
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand s.1 U t) ≤
        (ENNReal.ofReal B) ^ 2 * linearKSeminormIntegral s := by
    calc
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand s.1 U t) ≤
          ∫⁻ t in Set.Ioo (0 : ℝ) 1,
            (ENNReal.ofReal B) ^ 2 *
              ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) :=
        setLIntegral_mono' measurableSet_Ioo hintegrand
      _ = (ENNReal.ofReal B) ^ 2 * linearKSeminormIntegral s := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
        rfl
  rw [continuousKSeminorm_eq_lintegral]
  have hsqrt :
      ((ENNReal.ofReal B) ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal B := by
    simpa only [one_div] using!
      (ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) (ENNReal.ofReal B))
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        continuousKSeminormIntegrand s.1 U t) ^ (1 / 2 : ℝ) ≤
        ((ENNReal.ofReal B) ^ 2 * linearKSeminormIntegral s) ^
          (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hintegral (by norm_num)
    _ = ENNReal.ofReal B * linearKSeminormConstant s := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsqrt]
      rfl

/-- Unit-cube `H¹ → H^s` estimate in the exact Euclidean carrier.  The
right side retains the normalized `L²` and coordinate-gradient quantities
needed by the divergence-lift construction. -/
theorem euclideanHsESeminorm_unitEuclideanL2FieldOfCubeVectorH1_le
    {d : ℕ} (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    euclideanHsESeminorm s (unitEuclideanL2FieldOfCubeVectorH1 F) ≤
      euclideanHsToContinuousKSeminormConstant s d *
        ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
            (unitEuclideanL2FieldOfCubeVectorH1 F) +
          ENNReal.ofReal F.gradientCoordL2NormSum * linearKSeminormConstant s) := by
  calc
    euclideanHsESeminorm s (unitEuclideanL2FieldOfCubeVectorH1 F) ≤
        euclideanHsToContinuousKSeminormConstant s d *
          ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
              (unitEuclideanL2FieldOfCubeVectorH1 F) +
            continuousKSeminorm s (unitEuclideanL2FieldOfCubeVectorH1 F)) :=
      euclideanHsESeminorm_le_mul_normalizedEuclideanLpENorm_add_continuousKSeminorm
        s (unitEuclideanL2FieldOfCubeVectorH1 F)
    _ ≤ _ := by
      gcongr
      exact continuousKSeminorm_unitEuclideanL2FieldOfCubeVectorH1_le s F

/-- Euclidean `L²` packaging of a coordinatewise cube `H¹` vector field. -/
noncomputable def centeredEuclideanL2FieldOfCubeVectorH1
    {d : ℕ} {m : ℤ} (F : CubeVectorH1Function (originCube d m)) :
    CenteredCubeEuclideanL2Field d m :=
  { toField := F.toField
    euclideanMemL2 := by
      rw [memLp_piLp_iff]
      intro i
      simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        Function.comp_apply, PiLp.toLp_apply, HilbertVec.ofVec,
        CubeVectorH1Function.toField] using
        (F.coord i).memL2_normalizedCubeMeasure }

@[simp] theorem centeredEuclideanL2FieldOfCubeVectorH1_apply
    {d : ℕ} {m : ℤ} (F : CubeVectorH1Function (originCube d m)) (x : Vec d) :
    centeredEuclideanL2FieldOfCubeVectorH1 F x = F.toField x := rfl

private theorem cubeEuclideanWspKernel_smul
    {d : ℕ} (s : FractionalOrder) (p : FiniteLpExponent)
    (c : ℝ) (F : Vec d → Vec d) :
    cubeEuclideanWspKernel s p (fun x => c • F x) =
      c • cubeEuclideanWspKernel s p F := by
  funext z
  simp only [cubeEuclideanWspKernel_apply, Pi.smul_apply]
  rw [← smul_sub]
  change _ • (c • HilbertVec.ofVec (F z.1 - F z.2)) =
    c • (_ • HilbertVec.ofVec (F z.1 - F z.2))
  rw [smul_smul, smul_smul, mul_comm]

/-- Homogeneity of the exact positive fractional seminorm. -/
theorem cubeEuclideanWspESeminorm_smul
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (c : ℝ) (F : Vec d → Vec d) :
    cubeEuclideanWspESeminorm Q s p (fun x => c • F x) =
      ‖c‖ₑ * cubeEuclideanWspESeminorm Q s p F := by
  unfold cubeEuclideanWspESeminorm
  rw [cubeEuclideanWspKernel_smul]
  exact eLpNorm_const_smul c _ _ _

/-- On the centered unit cube, the cube `W^{s,2}` seminorm of an `H¹`
vector field is the exact unit Euclidean `H^s` seminorm used above. -/
theorem cubeEuclideanWspESeminorm_unitCubeVectorH1_eq_euclideanHs
    {d : ℕ} (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    cubeEuclideanWspESeminorm (originCube d 0) s FiniteLpExponent.two F.toField =
      euclideanHsESeminorm s (unitEuclideanL2FieldOfCubeVectorH1 F) := by
  let C : CenteredCubeEuclideanL2Field d 0 :=
    centeredEuclideanL2FieldOfCubeVectorH1 F
  rw [show F.toField = C.toField by rfl]
  rw [cubeEuclideanWspESeminorm_originCube_two_eq_centeredCubeEuclideanHsESeminorm
    s C]
  rw [centeredCubeEuclideanHsESeminorm_eq_scale_mul_pullbackToUnit]
  simp only [centeredCubeScale_zero, ENNReal.ofReal_one, one_mul,
    ENNReal.one_rpow]
  apply euclideanHsESeminorm_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    ext i
    change (F.coord i).toFun (1 • x) = (F.coord i).toFun x
    rw [one_smul]

/-- Exact fractional-seminorm scaling of the manuscript datum
`G(y)=alpha 3^{-m} F(3^{-m}y)`. -/
theorem cubeEuclideanWspESeminorm_centeredCubeScaledVectorDilation_eq
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    cubeEuclideanWspESeminorm (originCube d m) s FiniteLpExponent.two
        (centeredCubeScaledVectorDilation alpha m F).toField =
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
          euclideanHsESeminorm s (unitEuclideanL2FieldOfCubeVectorH1 F) := by
  have hcube : Homogenization.Book.Ch02.dilateCube m (originCube d 0) =
      originCube d m := by
    simp [Homogenization.Book.Ch02.dilateCube, originCube]
  have hdilate := cubeEuclideanWspESeminorm_dilate m (originCube d 0) s
    FiniteLpExponent.two
    (centeredCubeScaledVectorDilation alpha m F).toField
  rw [hcube] at hdilate
  rw [hdilate]
  have hfield :
      (fun x => (centeredCubeScaledVectorDilation alpha m F).toField
        (Homogenization.Book.Ch02.dilateVec m x)) =
        (fun x => (alpha * (centeredCubeScale m)⁻¹) • F.toField x) := by
    funext x
    rw [centeredCubeScaledVectorDilation_toField]
    have hscale : Homogenization.Book.Ch02.triadicDilationFactor m =
        centeredCubeScale m := rfl
    rw [Homogenization.Book.Ch02.dilateVec, hscale, smul_smul,
      inv_mul_cancel₀ (centeredCubeScale_ne_zero m), one_smul]
  rw [hfield, cubeEuclideanWspESeminorm_smul]
  rw [cubeEuclideanWspESeminorm_unitCubeVectorH1_eq_euclideanHs]
  simp only [Homogenization.Book.Ch02.triadicDilationFactor,
    centeredCubeScale, mul_assoc]

/-- The scaled datum's raw exact seminorm, before the manuscript's leading
`sqrt s` normalization. -/
theorem cubeEuclideanWspESeminorm_centeredCubeScaledVectorDilation_le
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    cubeEuclideanWspESeminorm (originCube d m) s FiniteLpExponent.two
        (centeredCubeScaledVectorDilation alpha m F).toField ≤
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
        (euclideanHsToContinuousKSeminormConstant s d *
          ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
              (unitEuclideanL2FieldOfCubeVectorH1 F) +
            ENNReal.ofReal F.gradientCoordL2NormSum * linearKSeminormConstant s)) := by
  rw [cubeEuclideanWspESeminorm_centeredCubeScaledVectorDilation_eq]
  let front : ℝ≥0∞ :=
    (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
      ‖alpha * (centeredCubeScale m)⁻¹‖ₑ
  have hunit := euclideanHsESeminorm_unitEuclideanL2FieldOfCubeVectorH1_le s F
  have hmul := mul_le_mul_right hunit front
  simpa only [front, mul_assoc] using hmul

/-- The manuscript datum as a proof-carrying finite `W^{s,2}` field on the
scale-`m` centered cube. -/
noncomputable def centeredCubeScaledVectorDilationWspField
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    CubeEuclideanWspField (originCube d m) s FiniteLpExponent.two := by
  let G : CubeVectorH1Function (originCube d m) :=
    centeredCubeScaledVectorDilation alpha m F
  let U : UnitCubeEuclideanL2Field d := unitEuclideanL2FieldOfCubeVectorH1 F
  have hLp : MemLp (fun x => HilbertVec.ofVec (G.toField x))
      FiniteLpExponent.two.exponent (normalizedCubeMeasure (originCube d m)) := by
    simpa only [FiniteLpExponent.two_exponent, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using!
      (centeredEuclideanL2FieldOfCubeVectorH1 G).euclideanMemL2
  have hLtop :
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) U < ∞ := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm] using
      U.euclideanMagnitudeMemL2.eLpNorm_lt_top
  have hbudgetTop :
      euclideanHsToContinuousKSeminormConstant s d *
          ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) U +
            ENNReal.ofReal F.gradientCoordL2NormSum * linearKSeminormConstant s) < ∞ := by
    exact ENNReal.mul_lt_top
      (euclideanHsToContinuousKSeminormConstant_lt_top s d)
      (ENNReal.add_lt_top.mpr ⟨hLtop,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (linearKSeminormConstant_lt_top s)⟩)
  have hscaleTop :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) < ∞ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rcases ENNReal.rpow_eq_top_iff.mp htop with hzero | htop'
    · exact (ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos m)) hzero.1
    · exact ENNReal.ofReal_ne_top htop'.1
  have hsemi : cubeEuclideanWspESeminorm (originCube d m) s
      FiniteLpExponent.two G.toField < ∞ := by
    apply lt_of_le_of_lt
      (cubeEuclideanWspESeminorm_centeredCubeScaledVectorDilation_le
        alpha m s F)
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hscaleTop enorm_lt_top) hbudgetTop
  exact
    { toField := G.toField
      euclideanMemLp := hLp
      euclideanMemWsp := memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top hLp hsemi }

@[simp] theorem centeredCubeScaledVectorDilationWspField_toField
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    (centeredCubeScaledVectorDilationWspField alpha m s F).toField =
      (centeredCubeScaledVectorDilation alpha m F).toField := rfl

/-- Positive fractional estimate for the scaled vector datum, with the exact
physical `3^{-ms}` factor and the unit `H¹` budget exposed. -/
theorem paperFractionalSeminorm_centeredCubeScaledVectorDilation_le
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    paperFractionalSeminorm (originCube d m) s FiniteLpExponent.two
        (centeredCubeScaledVectorDilation alpha m F).toField ≤
      (ENNReal.ofReal s.1) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
        (euclideanHsToContinuousKSeminormConstant s d *
          ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
              (unitEuclideanL2FieldOfCubeVectorH1 F) +
            ENNReal.ofReal F.gradientCoordL2NormSum * linearKSeminormConstant s)) := by
  unfold paperFractionalSeminorm
  norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
  rw [cubeEuclideanWspESeminorm_centeredCubeScaledVectorDilation_eq]
  let front : ℝ≥0∞ :=
    (ENNReal.ofReal s.1) ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        ‖alpha * (centeredCubeScale m)⁻¹‖ₑ
  have hunit := euclideanHsESeminorm_unitEuclideanL2FieldOfCubeVectorH1_le s F
  have hmul := mul_le_mul_right hunit front
  simpa only [front, mul_assoc] using hmul

/-! ### Finite manuscript-facing `H¹` budget -/

/-- The two unit-cube quantities retained by the interpolation proof,
packaged as one extended nonnegative `H¹` budget. -/
noncomputable def unitCubeVectorH1ENormBudget
    {d : ℕ} (F : CubeVectorH1Function (originCube d 0)) : ℝ≥0∞ :=
  (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      (unitEuclideanL2FieldOfCubeVectorH1 F) +
    ENNReal.ofReal F.gradientCoordL2NormSum

/-- The unit-cube Poisson construction gives the divergence lift in the
full `H¹` budget required by the positive fractional estimate. This
strengthens the gradient-only public lift exactly at the unit scale used by
the manuscript. -/
theorem exists_unitCubeVectorH1Function_divergence_lift_h1ENormBudget
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : Vec d → ℝ)
        (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0)))),
        ∃ F : CubeVectorH1Function (originCube d 0),
          (∀ phi : H10Function (openCubeSet (originCube d 0)),
            ∫ x in openCubeSet (originCube d 0),
                f x * phi.toH1Function.toFun x ∂volume =
              -∫ x in openCubeSet (originCube d 0),
                vecDot (F.toField x) (phi.toH1Function.grad x) ∂volume) ∧
          unitCubeVectorH1ENormBudget F ≤
            ENNReal.ofReal (C * ‖toScalarL2 hf‖) := by
  obtain ⟨C2, hC2⟩ :=
    Homogenization.CubeDirichletWeakPoissonProblem.exists_cubeDirichletH2RegularityVolumeL2InDimension d
  let C0 : ℝ :=
    Homogenization.CubeDirichletWeakPoissonProblem.originCubeZeroTraceH1HilbertCoerciveConstant d 0
  refine ⟨C0 + C2, add_nonneg
    (Homogenization.CubeDirichletWeakPoissonProblem.originCubeZeroTraceH1HilbertCoerciveConstant_nonneg d 0)
    hC2.1, ?_⟩
  intro f hf
  obtain ⟨u, hu⟩ :=
    exists_isScalarDirichletSolutionOn_one
      (Q := originCube d 0)
      (hD := (0 : H1Function (openCubeSet (originCube d 0)))) hf
  obtain ⟨w, _hvalue, hgrad⟩ := hu.1
  have hweak : CubeDirichletWeakPoissonProblem (originCube d 0) w f := by
    intro phi
    have heq := hu.2 phi
    simp_rw [hgrad] at heq
    simp only [Pi.zero_apply, H1Function.zero_grad, zero_add] at heq
    simp_rw [show ∀ x : Vec d, matVecMul (1 : Mat d) (w.toH1Function.grad x) =
        w.toH1Function.grad x from fun x ↦ Matrix.one_mulVec _] at heq
    exact heq
  have hfNormalized : MemLp f 2 (normalizedCubeMeasure (originCube d 0)) := by
    rw [normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
    exact hf
  obtain ⟨H, hH⟩ := (hC2.2 (originCube d 0)).2 w f hfNormalized hweak
  let G : CubeVectorH1Function (originCube d 0) :=
    CubeVectorH1Function.ofWeakHessianGradient H
  let F : CubeVectorH1Function (originCube d 0) := negCubeVectorH1Function G
  refine ⟨F, ?_, ?_⟩
  · intro phi
    have heq := hweak phi
    rw [← heq]
    simp only [F, G, negCubeVectorH1Function_toField,
      CubeVectorH1Function.ofWeakHessianGradient_toField]
    have hintegral :
        (∫ x in openCubeSet (originCube d 0),
          vecDot (-w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) =
          -(∫ x in openCubeSet (originCube d 0),
            vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) := by
      simp_rw [vecDot_neg_left]
      exact integral_neg _
    rw [hintegral, neg_neg]
  · have henergy :=
      Homogenization.CubeDirichletWeakPoissonProblem.norm_gradToHilbertVectorL2_le_solverCubeLpNorm_exact
        hweak hfNormalized
    have hnorm := norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two
      (originCube d 0) hfNormalized
    have henergy' : ‖w.toH1Function.gradToHilbertVectorL2‖ ≤
        C0 * ‖toScalarL2 hf‖ := by
      rw [← hnorm] at henergy
      simpa only [C0] using henergy
    have hfield :
        (fun x => HilbertVec.ofVec (F.toField x)) =
          fun x => -(hilbertifyVecField w.toH1Function.grad x) := by
      funext x
      simp only [F, G, negCubeVectorH1Function_toField,
        CubeVectorH1Function.ofWeakHessianGradient_toField]
      exact (HilbertVec.ofVecL d).map_neg _
    have hL :
        (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
            (unitEuclideanL2FieldOfCubeVectorH1 F) =
          ENNReal.ofReal ‖w.toH1Function.gradToHilbertVectorL2‖ := by
      unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
        BoundedMeasurableDomain.normalizedLpENorm
      rw [← normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
      simp only [unitEuclideanL2FieldOfCubeVectorH1_apply,
        euclideanNorm_eq_norm_ofVec]
      have hFm : AEStronglyMeasurable (fun x => HilbertVec.ofVec (F.toField x))
          (normalizedCubeMeasure (originCube d 0)) := by
        simpa only [unitEuclideanL2FieldOfCubeVectorH1_apply,
          normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume] using!
          (unitEuclideanL2FieldOfCubeVectorH1 F).euclideanMemL2.aestronglyMeasurable
      rw [eLpNorm_norm _ hFm, hfield]
      change eLpNorm (-(hilbertifyVecField w.toH1Function.grad)) 2
        (normalizedCubeMeasure (originCube d 0)) = _
      rw [eLpNorm_neg,
        normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
      exact
        Homogenization.CubeCalderonZygmund.eLpNorm_hilbertify_grad_two_eq_ofReal_norm_gradToHilbertVectorL2
          w.toH1Function
    have hgrad : F.gradientCoordL2NormSum ≤ C2 * ‖toScalarL2 hf‖ := by
      change (negCubeVectorH1Function G).gradientCoordL2NormSum ≤ _
      rw [negCubeVectorH1Function_gradientCoordL2NormSum]
      simpa only [G,
        CubeVectorH1Function.gradientCoordL2NormSum_ofWeakHessianGradient] using hH
    have hC0term : 0 ≤ C0 * ‖toScalarL2 hf‖ := mul_nonneg
      (Homogenization.CubeDirichletWeakPoissonProblem.originCubeZeroTraceH1HilbertCoerciveConstant_nonneg d 0)
      (norm_nonneg _)
    have hC2term : 0 ≤ C2 * ‖toScalarL2 hf‖ :=
      mul_nonneg hC2.1 (norm_nonneg _)
    unfold unitCubeVectorH1ENormBudget
    rw [hL]
    calc
      ENNReal.ofReal ‖w.toH1Function.gradToHilbertVectorL2‖ +
          ENNReal.ofReal F.gradientCoordL2NormSum ≤
        ENNReal.ofReal (C0 * ‖toScalarL2 hf‖) +
          ENNReal.ofReal (C2 * ‖toScalarL2 hf‖) :=
        add_le_add (ENNReal.ofReal_le_ofReal henergy')
          (ENNReal.ofReal_le_ofReal hgrad)
      _ = ENNReal.ofReal ((C0 * ‖toScalarL2 hf‖) +
          (C2 * ‖toScalarL2 hf‖)) :=
        (ENNReal.ofReal_add hC0term hC2term).symm
      _ = ENNReal.ofReal ((C0 + C2) * ‖toScalarL2 hf‖) := by
        congr 1
        ring

/-- The finite dimension/order constant which converts the unit `H¹` budget
to the paper positive fractional seminorm. -/
noncomputable def scaledVectorDatumFractionalConstant
    (s : FractionalOrder) (d : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal s.1) ^ (1 / 2 : ℝ) *
    euclideanHsToContinuousKSeminormConstant s d *
      max 1 (linearKSeminormConstant s)

theorem scaledVectorDatumFractionalConstant_lt_top
    (s : FractionalOrder) (d : ℕ) :
    scaledVectorDatumFractionalConstant s d < ∞ := by
  unfold scaledVectorDatumFractionalConstant
  apply ENNReal.mul_lt_top
  · exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      (euclideanHsToContinuousKSeminormConstant_lt_top s d)
  · rw [max_lt_iff]
    exact ⟨ENNReal.one_lt_top, linearKSeminormConstant_lt_top s⟩

/-- Finite extended-norm bound for the scaled manuscript datum. -/
noncomputable def scaledVectorDatumFractionalENormBound
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) : ℝ≥0∞ :=
  scaledVectorDatumFractionalConstant s d *
    (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
      ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
        unitCubeVectorH1ENormBudget F

theorem scaledVectorDatumFractionalENormBound_lt_top
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    scaledVectorDatumFractionalENormBound alpha m s F < ∞ := by
  have hscale :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) < ∞ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rcases ENNReal.rpow_eq_top_iff.mp htop with hzero | htop'
    · exact (ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos m)) hzero.1
    · exact ENNReal.ofReal_ne_top htop'.1
  have hLp :
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
          (unitEuclideanL2FieldOfCubeVectorH1 F) < ∞ := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm] using
      (unitEuclideanL2FieldOfCubeVectorH1 F).euclideanMagnitudeMemL2.eLpNorm_lt_top
  have hbudget : unitCubeVectorH1ENormBudget F < ∞ := by
    exact ENNReal.add_lt_top.mpr ⟨hLp, ENNReal.ofReal_lt_top⟩
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top
        (scaledVectorDatumFractionalConstant_lt_top s d) hscale)
      enorm_lt_top)
    hbudget

/-- The raw interpolation estimate with the unit `L²` and gradient terms
absorbed into one `H¹` budget. The triadic scale and datum amplitude remain
literal. -/
theorem paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_h1Budget
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    paperFractionalSeminorm (originCube d m) s FiniteLpExponent.two
        (centeredCubeScaledVectorDilation alpha m F).toField ≤
      scaledVectorDatumFractionalENormBound alpha m s F := by
  let L : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      (unitEuclideanL2FieldOfCubeVectorH1 F)
  let G : ℝ≥0∞ := ENNReal.ofReal F.gradientCoordL2NormSum
  let K : ℝ≥0∞ := linearKSeminormConstant s
  have hLK : L + G * K ≤ max 1 K * (L + G) := by
    calc
      L + G * K ≤ max 1 K * L + max 1 K * G := by
        apply add_le_add
        · simpa only [mul_one, one_mul, mul_comm] using
            mul_le_mul_right (le_max_left (1 : ℝ≥0∞) K) L
        · simpa only [mul_comm] using
            mul_le_mul_right (le_max_right (1 : ℝ≥0∞) K) G
      _ = max 1 K * (L + G) := by ring
  calc
    paperFractionalSeminorm (originCube d m) s FiniteLpExponent.two
          (centeredCubeScaledVectorDilation alpha m F).toField ≤
        (ENNReal.ofReal s.1) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
          ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
          (euclideanHsToContinuousKSeminormConstant s d * (L + G * K)) := by
      simpa only [L, G, K] using
        paperFractionalSeminorm_centeredCubeScaledVectorDilation_le alpha m s F
    _ ≤ (ENNReal.ofReal s.1) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
          ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
          (euclideanHsToContinuousKSeminormConstant s d *
            (max 1 K * (L + G))) := by gcongr
    _ = scaledVectorDatumFractionalENormBound alpha m s F := by
      unfold scaledVectorDatumFractionalENormBound
      unfold scaledVectorDatumFractionalConstant unitCubeVectorH1ENormBudget
      simp only [L, G, K]
      ring

/-- The manuscript's chosen divergence lift and scaled datum in one
statement: its positive fractional seminorm is bounded by the scalar forcing
norm with a dimension-only lift constant and the literal scale/amplitude
factors. -/
theorem exists_divergenceLift_paperFractionalSeminorm_scaled_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : Vec d → ℝ)
        (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))))
        (alpha : ℝ) (m : ℤ) (s : FractionalOrder),
        ∃ F : CubeVectorH1Function (originCube d 0),
          (∀ phi : H10Function (openCubeSet (originCube d 0)),
            ∫ x in openCubeSet (originCube d 0),
                f x * phi.toH1Function.toFun x ∂volume =
              -∫ x in openCubeSet (originCube d 0),
                vecDot (F.toField x) (phi.toH1Function.grad x) ∂volume) ∧
          paperFractionalSeminorm (originCube d m) s FiniteLpExponent.two
              (centeredCubeScaledVectorDilation alpha m F).toField ≤
            scaledVectorDatumFractionalConstant s d *
              (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
              ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
              ENNReal.ofReal (C * ‖toScalarL2 hf‖) := by
  obtain ⟨C, hC, hlift⟩ :=
    exists_unitCubeVectorH1Function_divergence_lift_h1ENormBudget d
  refine ⟨C, hC, ?_⟩
  intro f hf alpha m s
  obtain ⟨F, hpair, hbudget⟩ := hlift f hf
  refine ⟨F, hpair, ?_⟩
  exact
    (paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_h1Budget
      alpha m s F).trans (by
        unfold scaledVectorDatumFractionalENormBound
        exact mul_le_mul_right hbudget _)

/-- The finite real upper bound supplied to the real-valued coarse-graining
RHS interface. -/
noncomputable def scaledVectorDatumFractionalBound
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) : ℝ :=
  (scaledVectorDatumFractionalENormBound alpha m s F).toReal

theorem scaledVectorDatumFractionalBound_nonneg
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    0 ≤ scaledVectorDatumFractionalBound alpha m s F :=
  ENNReal.toReal_nonneg

/-- Manuscript-facing finite-real positive fractional estimate. -/
theorem paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_realBound
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    paperFractionalSeminorm (originCube d m) s FiniteLpExponent.two
        (centeredCubeScaledVectorDilation alpha m F).toField ≤
      ENNReal.ofReal (scaledVectorDatumFractionalBound alpha m s F) := by
  rw [scaledVectorDatumFractionalBound,
    ENNReal.ofReal_toReal
      (scaledVectorDatumFractionalENormBound_lt_top alpha m s F).ne]
  exact paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_h1Budget
    alpha m s F

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
