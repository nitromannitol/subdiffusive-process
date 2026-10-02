import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.DatumPricing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PositiveFractionalDatum
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry

/-!
# Full positive-Besov price from an exact Euclidean fractional datum

`DatumPricing` supplies the arbitrary-scale seminorm comparison.  The
Dirichlet energy consequence needs the full norm, so this file adds the
top-scale vector average, bounded coordinatewise by the exact Euclidean
normalized `L²` norm.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

/-- The Euclidean length of the cube average is controlled by a
dimension-only multiple of the direct Euclidean normalized `L²` norm. -/
theorem sqrt_vecNormSq_cubeAverageVec_le_dimension_mul_euclideanLp
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    Real.sqrt (vecNormSq (cubeAverageVec Q F.toField)) ≤
      (d : ℝ) *
        ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) F.toField).toReal := by
  let L : ℝ := ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
    (2 : ℝ≥0∞) F.toField).toReal
  let A : Fin d → ℝ := fun i ↦
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ F.toField x i)
  have hcoord : ∀ i : Fin d,
      MemLp (fun x ↦ F.toField x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := fun i ↦
    cubeEuclideanLp_coordinate_memLp F.toCubeEuclideanLpField i
  have hA0 : ∀ i : Fin d, 0 ≤ A i := fun i ↦ cubeLpNorm_nonneg Q 2 _
  have hA_le : ∀ i : Fin d, A i ≤ L := by
    intro i
    have hraw := coordinate_eLpNorm_le_euclidean
      (normalizedCubeMeasure Q) FiniteLpExponent.two F.toField i
    have htop := F.normalizedEuclideanLpENorm_lt_top
    unfold A L cubeLpNorm
    apply ENNReal.toReal_mono htop.ne
    unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
      BoundedMeasurableDomain.normalizedLpENorm
    simp only [euclideanNorm_eq_norm_ofVec]
    rw [eLpNorm_norm]
    simpa only [FiniteLpExponent.two_exponent,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using hraw
  have havg : ∀ i : Fin d,
      ‖cubeAverage Q (fun x ↦ F.toField x i)‖ ≤ A i := fun i ↦
    norm_cubeAverage_le_cubeLpNorm_two Q _ (hcoord i)
  have hsquares :
      vecNormSq (cubeAverageVec Q F.toField) ≤
        ∑ i : Fin d, (A i) ^ (2 : ℕ) := by
    unfold vecNormSq vecDot cubeAverageVec
    apply Finset.sum_le_sum
    intro i _
    have hi := havg i
    have hsq := (sq_le_sq₀ (abs_nonneg _) (hA0 i)).2 (by
      simpa only [Real.norm_eq_abs] using hi)
    calc
      cubeAverage Q (fun x ↦ F.toField x i) *
            cubeAverage Q (fun x ↦ F.toField x i) =
          ‖cubeAverage Q (fun x ↦ F.toField x i)‖ ^ (2 : ℕ) := by
            rw [Real.norm_eq_abs, sq_abs, pow_two]
      _ ≤ A i ^ (2 : ℕ) := hsq
  calc
    Real.sqrt (vecNormSq (cubeAverageVec Q F.toField)) ≤
        Real.sqrt (∑ i : Fin d, (A i) ^ (2 : ℕ)) :=
      Real.sqrt_le_sqrt hsquares
    _ ≤ ∑ i : Fin d, A i := by
      simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
        (sqrt_sum_sq_le_sum (Finset.univ : Finset (Fin d)) A
          (fun i _ ↦ hA0 i))
    _ ≤ ∑ _i : Fin d, L := Finset.sum_le_sum fun i _ ↦ hA_le i
    _ = (d : ℝ) * L := by simp

/-- Arbitrary-scale full positive-Besov price for the exact Euclidean
fractional carrier. -/
theorem scaleNormalizedPositiveBesovVectorNormTwo_le_exactDatum_general
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    scaleNormalizedPositiveBesovVectorNormTwo Q s.1 F.toField ≤
      (d : ℝ) *
          ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
            (2 : ℝ≥0∞) F.toField).toReal +
        caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1) Q *
          (cubeEuclideanWspESeminorm Q s FiniteLpExponent.two
            F.toField).toReal := by
  unfold scaleNormalizedPositiveBesovVectorNormTwo
  exact add_le_add
    (sqrt_vecNormSq_cubeAverageVec_le_dimension_mul_euclideanLp Q s F)
    (scaleNormalizedPositiveBesovVectorSeminormTwo_le_exactDatum_general Q s F)

/-! ### Physical forcing seminorm price -/

/-- Finite extended-real bound for the raw exact fractional seminorm of a
scaled coordinatewise `H¹` vector field. -/
noncomputable def scaledVectorDatumWspENormBound
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) : ℝ≥0∞ :=
  (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
    ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
      (euclideanHsToContinuousKSeminormConstant s d *
        (max 1 (linearKSeminormConstant s) *
          unitCubeVectorH1ENormBudget F))

theorem scaledVectorDatumWspENormBound_lt_top
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    scaledVectorDatumWspENormBound alpha m s F < ∞ := by
  have hscale :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) < ∞ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rcases ENNReal.rpow_eq_top_iff.mp htop with hzero | htop'
    · exact (ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos m)) hzero.1
    · exact ENNReal.ofReal_ne_top htop'.1
  have hbudget : unitCubeVectorH1ENormBudget F < ∞ := by
    unfold unitCubeVectorH1ENormBudget
    exact ENNReal.add_lt_top.mpr
      ⟨by
        simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
          BoundedMeasurableDomain.normalizedLpENorm] using
          (unitEuclideanL2FieldOfCubeVectorH1 F).euclideanMagnitudeMemL2.eLpNorm_lt_top,
        ENNReal.ofReal_lt_top⟩
  unfold scaledVectorDatumWspENormBound
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hscale enorm_lt_top)
    (ENNReal.mul_lt_top
      (euclideanHsToContinuousKSeminormConstant_lt_top s d)
      (ENNReal.mul_lt_top
        (max_lt_iff.mpr ⟨ENNReal.one_lt_top,
          linearKSeminormConstant_lt_top s⟩) hbudget))

/-- The exact fractional seminorm is controlled by the single unit `H¹`
budget, without the manuscript's extra leading `sqrt s`. -/
theorem cubeEuclideanWspESeminorm_centeredCubeScaledVectorDilation_le_h1Budget
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    cubeEuclideanWspESeminorm (originCube d m) s FiniteLpExponent.two
        (centeredCubeScaledVectorDilation alpha m F).toField ≤
      scaledVectorDatumWspENormBound alpha m s F := by
  let L : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      (unitEuclideanL2FieldOfCubeVectorH1 F)
  let G : ℝ≥0∞ := ENNReal.ofReal F.gradientCoordL2NormSum
  let K : ℝ≥0∞ := linearKSeminormConstant s
  have hLK : L + G * K ≤ max 1 K * (L + G) := by
    calc
      L + G * K ≤ max 1 K * L + max 1 K * G := by
        exact add_le_add
          (by simpa only [mul_one, one_mul, mul_comm] using
            mul_le_mul_right (le_max_left (1 : ℝ≥0∞) K) L)
          (by simpa only [mul_comm] using
            mul_le_mul_right (le_max_right (1 : ℝ≥0∞) K) G)
      _ = max 1 K * (L + G) := by ring
  calc
    _ ≤ (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
          (euclideanHsToContinuousKSeminormConstant s d * (L + G * K)) := by
      simpa only [L, G, K] using
        cubeEuclideanWspESeminorm_centeredCubeScaledVectorDilation_le
          alpha m s F
    _ ≤ (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
          (euclideanHsToContinuousKSeminormConstant s d *
            (max 1 K * (L + G))) := by gcongr
    _ = scaledVectorDatumWspENormBound alpha m s F := by
      unfold scaledVectorDatumWspENormBound unitCubeVectorH1ENormBudget
      simp only [L, G, K]

/-- Finite real positive-Besov seminorm price for the physical forcing. -/
noncomputable def scaledVectorDatumPositiveBesovSeminormBound
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) : ℝ :=
  caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1)
      (originCube d m) *
    (scaledVectorDatumWspENormBound alpha m s F).toReal

theorem scaledVectorDatumPositiveBesovSeminormBound_nonneg
    {d : ℕ} [NeZero d] (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    0 ≤ scaledVectorDatumPositiveBesovSeminormBound alpha m s F := by
  unfold scaledVectorDatumPositiveBesovSeminormBound
  exact mul_nonneg
    (mul_nonneg (caccioppoliExactDatumConstant_pos d).le
      (cubeBesovScaleWeight_nonneg _ _)) ENNReal.toReal_nonneg

theorem scaleNormalizedPositiveBesovVectorSeminormTwo_scaledVectorDatum_le
    {d : ℕ} [NeZero d] (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0)) :
    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d m) s.1
        (centeredCubeScaledVectorDilation alpha m F).toField ≤
      scaledVectorDatumPositiveBesovSeminormBound alpha m s F := by
  let G : CubeEuclideanWspField (originCube d m) s FiniteLpExponent.two :=
    centeredCubeScaledVectorDilationWspField alpha m s F
  have hbase := scaleNormalizedPositiveBesovVectorSeminormTwo_le_exactDatum_general
    (originCube d m) s G
  have hW := cubeEuclideanWspESeminorm_centeredCubeScaledVectorDilation_le_h1Budget
    alpha m s F
  have hWreal :
      (cubeEuclideanWspESeminorm (originCube d m) s FiniteLpExponent.two
          G.toField).toReal ≤
        (scaledVectorDatumWspENormBound alpha m s F).toReal := by
    apply ENNReal.toReal_mono
      (scaledVectorDatumWspENormBound_lt_top alpha m s F).ne
    simpa only [G, centeredCubeScaledVectorDilationWspField_toField] using hW
  apply hbase.trans
  unfold scaledVectorDatumPositiveBesovSeminormBound
  exact mul_le_mul_of_nonneg_left hWreal
    (mul_nonneg (caccioppoliExactDatumConstant_pos d).le
      (cubeBesovScaleWeight_nonneg _ _))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
