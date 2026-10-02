import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalTransport
import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS

/-!
# Pricing the rough fractional datum on an arbitrary cube

The public exact-datum comparison in `CaccioppoliRHS` is stated at the unit
origin cube.  The boundary cover uses origin cubes at arbitrary integer scale.
This module proves the scale-covariant form directly: the extra
`cubeBesovScaleWeight (-s) Q` is exactly the manuscript factor `3^(s k)`.

PROVENANCE: this is the normalization/index layer of
`Algsuperdiff/Section4/Provider/ExcessDecay/CoarseDatumPricing.lean`, adapted
to the v5 Euclidean `W^{s,2}` carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

private noncomputable def wspFieldOfFull {Q : TriadicCube d}
    {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    CubeEuclideanWspField Q s FiniteLpExponent.two where
  toField := f
  euclideanMemLp := hf.1
  euclideanMemWsp := hf.2

omit [NeZero d] in
@[simp] private theorem wspFieldOfFull_toField {Q : TriadicCube d}
    {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    (wspFieldOfFull hf).toField = f := rfl

/-- Arbitrary-scale form of the exact Euclidean-datum to positive-Besov
comparison. -/
theorem scaleNormalizedPositiveBesovVectorSeminormTwo_le_exactDatum_general
    (Q : TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 F.toField ≤
      caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1) Q *
        (cubeEuclideanWspESeminorm Q s
          FiniteLpExponent.two F.toField).toReal := by
  let K : ℝ≥0∞ := (d : ℝ≥0∞) *
    cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two
  let S : ℝ≥0∞ := cubeEuclideanWspESeminorm Q s
    FiniteLpExponent.two F.toField
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
          (fun x ↦ F.toField x i) ≤ Real.sqrt K.toReal * S.toReal := by
    intro i
    let A : ℝ≥0∞ := Gagliardo.cubeGagliardoESeminorm Q s.1 (2 : ℝ≥0∞)
      (fun x ↦ F.toField x i)
    have hsingle : A ^ (2 : ℕ) ≤
        cubeCoordinateGagliardoPowerEnergy Q s FiniteLpExponent.two F.toField := by
      dsimp [A, cubeCoordinateGagliardoPowerEnergy]
      norm_num
      exact Finset.single_le_sum
        (fun j _ ↦ zero_le
          ((Gagliardo.cubeGagliardoESeminorm Q s.1 (2 : ℝ≥0∞)
            (fun x ↦ F.toField x j)) ^ (2 : ℕ)))
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
        cubeBesovScaleWeight (-s.1) Q *
          ((d : ℝ) * (Real.sqrt K.toReal * S.toReal)) := by
    unfold Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
    apply mul_le_mul_of_nonneg_left _ (cubeBesovScaleWeight_nonneg _ _)
    calc
      ∑ i : Fin d, Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm
          Q s.1 (2 : ℝ≥0∞) (fun x ↦ F.toField x i) ≤
          ∑ _i : Fin d, Real.sqrt K.toReal * S.toReal :=
        Finset.sum_le_sum fun i _ ↦ hcoord i
      _ = (d : ℝ) * (Real.sqrt K.toReal * S.toReal) := by
        simp [mul_comm]
  calc
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 F.toField ≤
        ((3 : ℝ) ^ ((d : ℝ) / 2) *
          Homogenization.Book.Ch01.Legacy.wspVsBsppConstant d) *
          Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
            Q s.1 F.toField := hbesov
    _ ≤ ((3 : ℝ) ^ ((d : ℝ) / 2) *
        Homogenization.Book.Ch01.Legacy.wspVsBsppConstant d) *
        (cubeBesovScaleWeight (-s.1) Q *
          ((d : ℝ) * (Real.sqrt K.toReal * S.toReal))) := by
      apply mul_le_mul_of_nonneg_left hsob
      unfold Homogenization.Book.Ch01.Legacy.wspVsBsppConstant
      positivity
    _ = caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1) Q *
        S.toReal := by
      simp only [caccioppoliExactDatumConstant, K, S]
      ring

/-- The arbitrary-scale Besov price written entirely in the frozen seminorm
carrier. -/
theorem scaleNormalizedPositiveBesovVectorSeminormTwo_le_fractionalSeminormOn
    (Q : TriadicCube d) (s : FractionalOrder) (f : Vec d → Vec d)
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 f ≤
      caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1) Q *
        (Real.rpow s.1 (-(1 / 2 : ℝ)) *
          (fractionalSeminormOn (openCubeSet Q) s.1 f).toReal) := by
  have h := scaleNormalizedPositiveBesovVectorSeminormTwo_le_exactDatum_general
    Q s (wspFieldOfFull hf)
  rw [wspFieldOfFull_toField,
    cubeEuclideanWspESeminorm_toReal_eq_rpow_neg_half_mul_fractional] at h
  exact h

/-- Pricing after transporting a covering cube into a larger manuscript
window.  The only geometric loss is the square root of the volume ratio. -/
theorem scaleNormalizedPositiveBesovVectorSeminormTwo_translate_le_window
    (Q : TriadicCube d) (c : Vec d) (U : Set (Vec d))
    (s : FractionalOrder) (f : Vec d → Vec d)
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two (fun x ↦ f (x + c)))
    (hsub : translateSet c (openCubeSet Q) ⊆ U)
    (hQ0 : volume (translateSet c (openCubeSet Q)) ≠ 0)
    (hQtop : volume (translateSet c (openCubeSet Q)) ≠ ∞)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hUfin : fractionalSeminormOn U s.1 f ≠ ∞) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 (fun x ↦ f (x + c)) ≤
      caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1) Q *
        (Real.rpow s.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal /
              (volume (translateSet c (openCubeSet Q))).toReal) *
            (fractionalSeminormOn U s.1 f).toReal)) := by
  have hbase := scaleNormalizedPositiveBesovVectorSeminormTwo_le_fractionalSeminormOn
    Q s (fun x ↦ f (x + c)) hf
  have hmono := fractionalSeminormOn_toReal_mono_set hsub hQ0 hQtop hU0 hUtop
    s.1 f hUfin
  rw [fractionalSeminormOn_translateSet c (openCubeSet Q) s.1 f] at hmono
  have hinner : Real.rpow s.1 (-(1 / 2 : ℝ)) *
        (fractionalSeminormOn (openCubeSet Q) s.1 (fun x ↦ f (x + c))).toReal ≤
      Real.rpow s.1 (-(1 / 2 : ℝ)) *
        (Real.sqrt ((volume U).toReal /
            (volume (translateSet c (openCubeSet Q))).toReal) *
          (fractionalSeminormOn U s.1 f).toReal) :=
    mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg s.2.1.le _)
  have hcoef : 0 ≤ caccioppoliExactDatumConstant d *
      cubeBesovScaleWeight (-s.1) Q :=
    mul_nonneg (caccioppoliExactDatumConstant_pos d).le
      (cubeBesovScaleWeight_nonneg _ _)
  exact hbase.trans (mul_le_mul_of_nonneg_left hinner hcoef)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
