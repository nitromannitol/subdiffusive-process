import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import Homogenization.Book.Ch03.Theorems.Inhomogeneous

/-!
# Bridges between the printed forced-equation carriers and the CoarseGraining library

The printed statement of `l.coarse.graining.RHS` is phrased with `ABK26.IsForcedEquation` (weak form
`∫ a ∇u · ∇φ = -∫ g · ∇φ`), the paper-normalized norms of `SubdiffusiveProcess.CoarseGrainingVocab.Norms`, and
`CubeEuclideanWspField` data.  The library theorems `Ch03.coarsePoincareRHSTheory`,
`Ch03.weakFluxRHSTheory`, `Ch03.energyConsequencesRHSTheory` are phrased with `Ch03.IsForcedEquation`
(weak form `∫ a ∇u · ∇φ = +∫ g · ∇φ`) and the library norms.  This module records the elementary
translations, uniformly in the cube `Q`.
-/

namespace SubdiffusiveProcess.CoarseRHS

open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec Mat TriadicCube

/-- The library `H¹` energy norm of a function equals the printed coefficient energy norm of its
gradient. -/
theorem h1Energy_eq {d : ℕ} (Q : Homogenization.TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (u : H1Function (openCubeSet Q)) :
    Ch03.h1EnergyNormOnCube Q a u = coefficientEnergyNorm Q a u.grad := by
  unfold Ch03.h1EnergyNormOnCube coefficientEnergyNorm Ch03.localizedCoeffEnergyValue
    Ch03.normalizedSetAverage
  congr 1
  rw [volumeAverage_openCubeSet_eq_cubeAverage, cubeAverage_eq_integral_normalizedCubeMeasure]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [vecDot_matVecMul_symmPart]

theorem vecDot_neg_left' {d : ℕ} (x y : Homogenization.Vec d) :
    vecDot (-x) y = -vecDot x y := by
  simp [vecDot]

/-- The printed sign convention (`-∇·a∇u = ∇·g`) is the library one for `-g`. -/
theorem isForced_neg {d : ℕ} {Q : Homogenization.TriadicCube d} {a : Ch02.TriadicCoeffFamily d}
    {u : H1Function (openCubeSet Q)} {g : Homogenization.Vec d → Homogenization.Vec d}
    (h : Ch03.ABK26.IsForcedEquation Q (a.coeffOn Q) u g) :
    Ch03.IsForcedEquation Q a u (fun x => -g x) := by
  intro φ
  have := h φ
  simp only [vecDot_neg_left', MeasureTheory.integral_neg]
  exact this

/-- General-scale version of `scaleNormalizedPositiveBesovVectorSeminormTwo_le_exactDatum`. -/
theorem besovPos_le_datum_general
    (d : ℕ) [NeZero d] (Q : Homogenization.TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 F.toField ≤
      caccioppoliExactDatumConstant d * Real.rpow (cubeScaleFactor Q) s.1 *
        (cubeEuclideanWspESeminorm Q s FiniteLpExponent.two F.toField).toReal := by
  let K : ℝ≥0∞ := (d : ℝ≥0∞) *
    cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two
  let S : ℝ≥0∞ := cubeEuclideanWspESeminorm Q s FiniteLpExponent.two F.toField
  have hreg := cubeEuclideanWspField_forceSobolevRegularity s F
  have hbesov :=
    Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveBesovVectorSeminormTwo_le_const_mul_sobolev
      Q F.toField s.2.1 s.2.2.le hreg
  have henergy := cubeCoordinateGagliardoPowerEnergy_le_dimension_mul_ambientHilbert
    Q s FiniteLpExponent.two F.toField
  have hambient := cubeAmbientHilbertWspESeminorm_rpow_le_metricComparisonConstant_mul
    Q s FiniteLpExponent.two F.toField
  have hsum_pow : cubeCoordinateGagliardoPowerEnergy Q s FiniteLpExponent.two F.toField ≤
      K * S ^ (2 : ℕ) := by
    dsimp [K, S]
    norm_num at henergy hambient ⊢
    exact henergy.trans (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_left hambient (d : ℝ≥0∞)))
  have hKtop : K ≠ ∞ := (ENNReal.mul_lt_top (ENNReal.natCast_lt_top d)
    (cubeEuclideanWspMetricComparisonConstant_lt_top d FiniteLpExponent.two)).ne
  have hStop : S ≠ ∞ := F.eSeminorm_lt_top.ne
  have hcoord : ∀ i : Fin d,
      Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm Q s.1 (2 : ℝ≥0∞)
          (fun x => F.toField x i) ≤ Real.sqrt K.toReal * S.toReal := by
    intro i
    let A : ℝ≥0∞ := Gagliardo.cubeGagliardoESeminorm Q s.1 (2 : ℝ≥0∞)
      (fun x => F.toField x i)
    have hsingle : A ^ (2 : ℕ) ≤
        cubeCoordinateGagliardoPowerEnergy Q s FiniteLpExponent.two F.toField := by
      dsimp [A, cubeCoordinateGagliardoPowerEnergy]
      norm_num
      exact Finset.single_le_sum
        (fun j _ => zero_le
          ((Gagliardo.cubeGagliardoESeminorm Q s.1 (2 : ℝ≥0∞)
            (fun x => F.toField x j)) ^ (2 : ℕ)))
        (Finset.mem_univ i)
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKtop (ENNReal.pow_ne_top hStop))
      (hsingle.trans hsum_pow)
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow] at hreal
    have hright : 0 ≤ Real.sqrt K.toReal * S.toReal := by positivity
    have hsq : (Real.sqrt K.toReal * S.toReal) ^ 2 = K.toReal * S.toReal ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
    dsimp [Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm,
      Gagliardo.cubeGagliardoSeminorm, A]
    apply (sq_le_sq₀ ENNReal.toReal_nonneg hright).mp
    simpa [hsq] using hreal
  have hsob :
      Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
          Q s.1 F.toField ≤
        Real.rpow (cubeScaleFactor Q) s.1 * ((d : ℝ) * (Real.sqrt K.toReal * S.toReal)) := by
    unfold Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
    have hw : cubeBesovScaleWeight (-s.1) Q = Real.rpow (cubeScaleFactor Q) s.1 := by
      unfold cubeBesovScaleWeight
      rw [neg_neg]; rfl
    rw [hw]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by unfold cubeScaleFactor; positivity) _)
    calc
      ∑ i : Fin d, Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm
          Q s.1 (2 : ℝ≥0∞)
          (fun x => F.toField x i) ≤
          ∑ _i : Fin d, Real.sqrt K.toReal * S.toReal :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * (Real.sqrt K.toReal * S.toReal) := by
        simp [mul_comm]
  calc
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 F.toField ≤
        ((3 : ℝ) ^ ((d : ℝ) / 2) *
          Homogenization.Book.Ch01.Legacy.wspVsBsppConstant d) *
          Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
            Q s.1 F.toField :=
      hbesov
    _ ≤ ((3 : ℝ) ^ ((d : ℝ) / 2) *
        Homogenization.Book.Ch01.Legacy.wspVsBsppConstant d) *
        (Real.rpow (cubeScaleFactor Q) s.1 * ((d : ℝ) * (Real.sqrt K.toReal * S.toReal))) := by
      apply mul_le_mul_of_nonneg_left hsob
      unfold Homogenization.Book.Ch01.Legacy.wspVsBsppConstant
      positivity
    _ = caccioppoliExactDatumConstant d * Real.rpow (cubeScaleFactor Q) s.1 * S.toReal := by
      simp only [caccioppoliExactDatumConstant, K, S]
      ring

/-- Unfolding of the paper seminorm at the Hilbert exponent. -/
theorem paperSem_toReal {d : ℕ} (Q : Homogenization.TriadicCube d) (s : FractionalOrder)
    (F : Homogenization.Vec d → Homogenization.Vec d) :
    (paperFractionalSeminorm Q s FiniteLpExponent.two F).toReal =
      Real.rpow s.1 (1 / 2 : ℝ) *
        (cubeEuclideanWspESeminorm Q s FiniteLpExponent.two F).toReal := by
  unfold paperFractionalSeminorm
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal s.2.1.le]
  have : (FiniteLpExponent.two.exponent).toReal = 2 := by simp [FiniteLpExponent.two]
  rw [this]
  simp [Real.rpow_eq_pow, one_div]

theorem paperFull_finite {d : ℕ} (Q : Homogenization.TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    paperFractionalFullNorm Q s FiniteLpExponent.two F.toField ≠ ⊤ := by
  unfold paperFractionalFullNorm paperFractionalSeminorm
  have hcf : (0 : ℝ) < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · refine ENNReal.mul_ne_top ?_ F.eSeminorm_lt_top.ne
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  · refine ENNReal.mul_ne_top ?_ F.normalizedEuclideanLpENorm_lt_top.ne
    rw [Ne, ENNReal.rpow_eq_top_iff]
    push_neg
    refine ⟨fun h => absurd h ?_, fun h => absurd h ENNReal.ofReal_ne_top⟩
    exact (ENNReal.ofReal_pos.mpr hcf).ne'

/-- The Euclidean norm of the cube average is bounded by the normalized `L²` norm. -/
theorem sqrt_vecNormSq_avg_le {d : ℕ} (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Vec d → Homogenization.Vec d)
    (hmem : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ENNReal.ofReal (Real.sqrt (vecNormSq (cubeAverageVec Q F))) ≤
      eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (normalizedCubeMeasure Q) := by
  let μ := normalizedCubeMeasure Q
  letI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hintegrable : Integrable (fun x => HilbertVec.ofVec (F x)) μ :=
    (hmem.mono_exponent (show (1 : ℝ≥0∞) ≤ 2 by norm_num)).integrable (by norm_num)
  have hmean : cubeAverageVec Q F = (∫ x, HilbertVec.ofVec (F x) ∂μ).toVec := by
    funext i
    simp only [cubeAverageVec, cubeAverage_eq_integral_normalizedCubeMeasure]
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      (eval_integral_piLp (fun j => hintegrable.eval_piLp j) i).symm
  calc
    ENNReal.ofReal (Real.sqrt (vecNormSq (cubeAverageVec Q F))) =
        ‖∫ x, HilbertVec.ofVec (F x) ∂μ‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← HilbertVec.ofVec_toVec (∫ x, HilbertVec.ofVec (F x) ∂μ),
        ← hmean, ← euclideanNorm_eq_norm_ofVec]
      rfl
    _ ≤ ∫⁻ x, ‖HilbertVec.ofVec (F x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => HilbertVec.ofVec (F x)) 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 μ :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hmem.aestronglyMeasurable

end SubdiffusiveProcess.CoarseRHS
