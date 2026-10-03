module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section2Support
public import SubdiffusiveProcess.CoarseGrainingVocab.PaperFractionalDualBridge
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.Theory
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.PublicRHSMonotonicity
public import Homogenization.Book.Ch03.Theorems.SobolevPublic
public import Homogenization.Sobolev.Fractional.ExactOverlapEuclideanLpComparison

@[expose] public section

/-!
# Coarse Caccioppoli with forcing on the D-024 range

This module is the ordinary support layer for ERRATA E-01.  On `0 < t ≤ 1/4`,
the forcing coefficient in CoarseGraining's packaged boundary theorem satisfies

```text
t⁻⁸ / (1 - 2t) ≤ 2 t⁻⁸ ≤ 2 t⁻¹¹.
```

The factor `2` is absorbed by enlarging the theorem's dimension-only constant.

PROVENANCE: the wrapper reuses
`Homogenization.Book.Ch03.CoarseCaccioppoliRHSTheory` and mirrors the
constant-enlargement split in
`Algsuperdiff/Section4/Provider/ExcessDecay/CaccioppoliInteriorPrefactor.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section






theorem cubeEuclideanWspField_forceSobolevRegularity {d : ℕ} [NeZero d]
    {Q : TriadicCube d} (s : FractionalOrder)
    (F : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity Q s.1 F.toField := by
  intro i
  refine ⟨cubeEuclideanLp_coordinate_memLp F.toCubeEuclideanLpField i, ?_⟩
  let G : Vec d → Vec d := F.toCubeEuclideanLpField.measurableRepresentative
  have hFG : F.toField =ᵐ[normalizedCubeMeasure Q] G :=
    F.toCubeEuclideanLpField.ae_eq_measurableRepresentative
  have hFGi : (fun x => F.toField x i) =ᵐ[cubeMeasure Q] (fun x => G x i) := by
    apply Gagliardo.ae_normalizedCubeMeasure_iff.mp
    filter_upwards [hFG] with x hx
    exact congrFun hx i
  apply (Gagliardo.memWsp_congr_ae hFGi).mpr
  rw [Gagliardo.memWsp_iff]
  constructor
  · have hG : Measurable G :=
      F.toCubeEuclideanLpField.measurable_measurableRepresentative
    unfold Gagliardo.gagliardoKernel
    apply Measurable.aestronglyMeasurable
    simpa only [Pi.smul_def, Pi.sub_def] using!
      (measurable_dist.pow measurable_const).smul
        (((continuous_apply i).measurable.comp (hG.comp measurable_fst)).sub
          ((continuous_apply i).measurable.comp (hG.comp measurable_snd)))
  · rw [← Gagliardo.cubeGagliardoESeminorm_congr_ae hFGi]
    let E : ℝ≥0∞ := Gagliardo.cubeGagliardoESeminorm Q s.1
      FiniteLpExponent.two.exponent (fun x => F.toField x i)
    have hsingle : E ^ FiniteLpExponent.two.exponent.toReal ≤
        cubeCoordinateGagliardoPowerEnergy Q s FiniteLpExponent.two F.toField := by
      dsimp [E, cubeCoordinateGagliardoPowerEnergy]
      simpa only using! (Finset.single_le_sum (f := fun j : Fin d =>
        (Gagliardo.cubeGagliardoESeminorm Q s.1
          FiniteLpExponent.two.exponent (fun x => F.toField x j)) ^
            FiniteLpExponent.two.exponent.toReal)
        (fun j _ => zero_le) (Finset.mem_univ i))
    have henergy := cubeCoordinateGagliardoPowerEnergy_le_dimension_mul_ambientHilbert
      Q s FiniteLpExponent.two F.toField
    have hambient := cubeAmbientHilbertWspESeminorm_rpow_le_metricComparisonConstant_mul
      Q s FiniteLpExponent.two F.toField (by
        letI : MeasureTheory.IsFiniteMeasure (cubeMeasure Q) :=
          ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top Q)⟩
        have hF := F.euclideanMemLp.aestronglyMeasurable
        have hFc : MeasureTheory.AEStronglyMeasurable
            (fun x => HilbertVec.ofVec (F.toField x)) (cubeMeasure Q) := by
          exact ⟨hF.mk _, hF.stronglyMeasurable_mk,
            Gagliardo.ae_normalizedCubeMeasure_iff.mp hF.ae_eq_mk⟩
        simpa only [cubeAmbientHilbertWspKernel, Function.comp_def,
          Pi.sub_def, Pi.smul_def, HilbertVec.ofVec] using!
          (measurable_dist.pow measurable_const).aestronglyMeasurable.smul
            ((hF.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_fst).sub
              (hFc.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_snd)))
    have htop :
        (d : ℝ≥0∞) * cubeEuclideanWspMetricComparisonConstant d
            FiniteLpExponent.two *
          (cubeEuclideanWspESeminorm Q s FiniteLpExponent.two F.toField) ^
            FiniteLpExponent.two.exponent.toReal < ∞ := by
      exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (ENNReal.natCast_lt_top d)
          (cubeEuclideanWspMetricComparisonConstant_lt_top d FiniteLpExponent.two))
        (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg F.eSeminorm_lt_top.ne)
    have hpow : E ^ FiniteLpExponent.two.exponent.toReal < ∞ := by
      refine lt_of_le_of_lt (hsingle.trans (henergy.trans ?_)) htop
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_left hambient (d : ℝ≥0∞))
    have hr : 0 < FiniteLpExponent.two.exponent.toReal := by norm_num
    exact (ENNReal.rpow_lt_top_iff_of_pos hr).mp hpow

/-- A dimension-only real constant for the exact-to-legacy positive datum
comparison at the Hilbert exponent. -/
noncomputable def caccioppoliExactDatumConstant (d : ℕ) : ℝ :=
  (3 : ℝ) ^ ((d : ℝ) / 2) *
    Homogenization.Book.Ch01.Legacy.wspVsBsppConstant d *
    (d : ℝ) *
      Real.sqrt (((d : ℝ≥0∞) *
        cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two).toReal)

theorem caccioppoliExactDatumConstant_pos (d : ℕ) [NeZero d] :
    0 < caccioppoliExactDatumConstant d := by
  unfold caccioppoliExactDatumConstant
  have hmetric : 0 < ((d : ℝ≥0∞) *
      cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two).toReal := by
    rw [ENNReal.toReal_pos_iff]
    constructor
    · exact ENNReal.mul_pos (Nat.cast_ne_zero.mpr (NeZero.ne d))
        (by
          apply ne_of_gt
          unfold cubeEuclideanWspMetricComparisonConstant
          have hdR : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
          positivity)
    · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top d)
        (cubeEuclideanWspMetricComparisonConstant_lt_top d
          FiniteLpExponent.two)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hpow : 0 < (3 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hlegacy : 0 < Homogenization.Book.Ch01.Legacy.wspVsBsppConstant d := by
    unfold Homogenization.Book.Ch01.Legacy.wspVsBsppConstant
    positivity
  exact mul_pos (mul_pos (mul_pos hpow hlegacy) hdR) (Real.sqrt_pos.mpr hmetric)

/-- At the origin cube, the packaged positive-Besov seminorm is controlled
by a dimension-only multiple of the exact Euclidean Gagliardo seminorm. -/
theorem scaleNormalizedPositiveBesovVectorSeminormTwo_le_exactDatum
    (d : ℕ) [NeZero d] (s : FractionalOrder)
    (F : CubeEuclideanWspField (originCube d 0) s FiniteLpExponent.two) :
    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d 0) s.1 F.toField ≤
      caccioppoliExactDatumConstant d *
        (cubeEuclideanWspESeminorm (originCube d 0) s
          FiniteLpExponent.two F.toField).toReal := by
  let Q : TriadicCube d := originCube d 0
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
    Q s FiniteLpExponent.two F.toField (by
      letI : MeasureTheory.IsFiniteMeasure (cubeMeasure Q) :=
        ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top Q)⟩
      have hF := F.euclideanMemLp.aestronglyMeasurable
      have hFc : MeasureTheory.AEStronglyMeasurable
          (fun x => HilbertVec.ofVec (F.toField x)) (cubeMeasure Q) := by
        exact ⟨hF.mk _, hF.stronglyMeasurable_mk,
          Gagliardo.ae_normalizedCubeMeasure_iff.mp hF.ae_eq_mk⟩
      simpa only [cubeAmbientHilbertWspKernel, Function.comp_def,
        Pi.sub_def, Pi.smul_def, HilbertVec.ofVec] using!
        (measurable_dist.pow measurable_const).aestronglyMeasurable.smul
          ((hF.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_fst).sub
            (hFc.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_snd)))
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
      simpa only using! (Finset.single_le_sum (f := fun j : Fin d =>
        (Gagliardo.cubeGagliardoESeminorm Q s.1 (2 : ℝ≥0∞)
          (fun x => F.toField x j)) ^ (2 : ℕ))
        (fun j _ => zero_le) (Finset.mem_univ i))
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
        (d : ℝ) * (Real.sqrt K.toReal * S.toReal) := by
    unfold Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
    have hQscale : Q.scale = 0 := rfl
    rw [show cubeBesovScaleWeight (-s.1) Q = 1 by
      unfold cubeBesovScaleWeight cubeScaleFactor
      rw [hQscale]
      norm_num]
    simp only [one_mul]
    calc
      ∑ i : Fin d, Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm
          Q s.1 (2 : ℝ≥0∞)
          (fun x => F.toField x i) ≤
          ∑ _i : Fin d, Real.sqrt K.toReal * S.toReal :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * (Real.sqrt K.toReal * S.toReal) := by
        simp [mul_comm]
  calc
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 F.toField ≤
        ((3 : ℝ) ^ ((d : ℝ) / 2) *
          Homogenization.Book.Ch01.Legacy.wspVsBsppConstant d) *
          Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
            Q s.1 F.toField :=
      hbesov
    _ ≤ ((3 : ℝ) ^ ((d : ℝ) / 2) *
        Homogenization.Book.Ch01.Legacy.wspVsBsppConstant d) *
        ((d : ℝ) * (Real.sqrt K.toReal * S.toReal)) := by
      apply mul_le_mul_of_nonneg_left hsob
      unfold Homogenization.Book.Ch01.Legacy.wspVsBsppConstant
      positivity
    _ = caccioppoliExactDatumConstant d * S.toReal := by
      simp only [caccioppoliExactDatumConstant, K, S, Q]
      ring

/-- Negation stays inside the exact Euclidean fractional carrier. -/
noncomputable def negCubeEuclideanWspField {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) : CubeEuclideanWspField Q s p where
  toField := fun x => -F.toField x
  euclideanMemLp := by
    have hfun : (fun x => HilbertVec.ofVec (-F.toField x)) =
        -(fun x => HilbertVec.ofVec (F.toField x)) := by
      funext x
      ext i
      simp [HilbertVec.ofVec]
    rw [hfun]
    exact F.euclideanMemLp.neg
  euclideanMemWsp := by
    show MeasureTheory.MemLp (cubeEuclideanWspKernel s p (fun x => -F.toField x))
      p.exponent (Gagliardo.gagliardoCubeMeasure Q)
    have hkernel : cubeEuclideanWspKernel s p (fun x => -F.toField x) =
        -cubeEuclideanWspKernel s p F.toField := by
      funext z
      ext i
      simp [cubeEuclideanWspKernel, HilbertVec.ofVec]
      ring
    rw [hkernel]
    exact F.euclideanMemWsp.neg

@[simp] theorem negCubeEuclideanWspField_toField {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) :
    (negCubeEuclideanWspField F).toField = fun x => -F.toField x := rfl

@[simp] theorem cubeEuclideanWspESeminorm_neg {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d) :
    cubeEuclideanWspESeminorm Q s p (fun x => -F x) =
      cubeEuclideanWspESeminorm Q s p F := by
  unfold cubeEuclideanWspESeminorm cubeEuclideanWspKernel
  have hfun :
      (fun z : Vec d × Vec d =>
        euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal)) •
          HilbertVec.ofVec ((-F z.1) - (-F z.2))) =
      -(fun z : Vec d × Vec d =>
        euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal)) •
          HilbertVec.ofVec (F z.1 - F z.2)) := by
    funext z
    ext i
    simp [HilbertVec.ofVec]
    ring
  rw [hfun]
  exact
    (MeasureTheory.eLpNorm_neg
      (fun z : Vec d × Vec d =>
        (euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
          HilbertVec.ofVec (F z.1 - F z.2))
      p.exponent (Gagliardo.gagliardoCubeMeasure Q))

/-- The power-aggregated exact full norm dominates its seminorm component. -/
theorem cubeEuclideanWspESeminorm_le_fullENorm {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d) :
    cubeEuclideanWspESeminorm Q s p F ≤
      cubeEuclideanWspFullENorm Q s p F := by
  let W := cubeEuclideanWspScalePowerWeight Q s p
  let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent F
  let S := cubeEuclideanWspESeminorm Q s p F
  let r := p.exponent.toReal
  have hr : 0 < r :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hpower : S ^ r ≤ W * L ^ r + S ^ r := le_add_of_nonneg_left bot_le
  have hroot := ENNReal.rpow_le_rpow hpower (inv_nonneg.mpr hr.le)
  rw [cubeEuclideanWspFullENorm]
  change S ≤ (W * L ^ r + S ^ r) ^ r⁻¹
  calc
    S = S ^ (r * r⁻¹) := by rw [mul_inv_cancel₀ hr.ne', ENNReal.rpow_one]
    _ = (S ^ r) ^ r⁻¹ := by rw [ENNReal.rpow_mul]
    _ ≤ (W * L ^ r + S ^ r) ^ r⁻¹ := hroot

/-- The entropy factor omitted by the printed Caccioppoli display is absorbed
by a uniform enlargement of its base constant. -/
theorem caccioppoli_entropy_and_constant_absorption
    {C₀ K s t : ℝ} (hC₀ : 0 < C₀) (hK : 1 ≤ K)
    (hs : 0 < s) (hs_one : s < 1) (ht : 0 < t) (ht_quarter : t ≤ 1 / 4)
    (hst : s + t < 1) :
    K *
        (Real.rpow (C₀ / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
          Real.rpow s (-(2 * s / (1 - s - t)))) ≤
      Real.rpow (((Real.exp 2 * K) ^ 2 * C₀) / (1 - s - t))
        (2 + 4 * s / (1 - s - t)) := by
  let σ : ℝ := 1 - s - t
  let p : ℝ := 2 + 4 * s / σ
  let A : ℝ := Real.exp 2 * K
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσ_one : σ ≤ 1 := by dsimp [σ]; linarith
  have hp_one : 1 ≤ p := by
    dsimp [p]
    have : 0 ≤ 4 * s / σ := by positivity
    linarith
  have hp_invσ : σ⁻¹ ≤ p := by
    calc
      σ⁻¹ = 1 / σ := (one_div σ).symm
      _ ≤ p := by
        rw [div_le_iff₀ hσ]
        have hpσ : p * σ = 2 * σ + 4 * s := by
          dsimp [p]
          field_simp [hσ.ne']
        rw [hpσ]
        dsimp [σ]
        nlinarith
  have hA_one : 1 ≤ A := by
    dsimp [A]
    have : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    nlinarith
  have hK_Ap : K ≤ Real.rpow A p := by
    calc
      K ≤ A := by
        dsimp [A]
        have hexp : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
        nlinarith
      _ ≤ Real.rpow A p := Real.self_le_rpow_of_one_le hA_one hp_one
  have hentropy : Real.rpow s (-(2 * s)) ≤ Real.exp 2 :=
    rpow_neg_two_mul_self_le_exp_two hs hs_one.le
  have hfactor : Real.rpow s (-(2 * s / σ)) ≤ Real.rpow A p := by
    have hinvσ : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
    calc
      Real.rpow s (-(2 * s / σ)) =
          Real.rpow s ((-(2 * s)) * σ⁻¹) := by
        congr 1
        rw [inv_eq_one_div]
        field_simp [hσ.ne']
      _ = Real.rpow (Real.rpow s (-(2 * s))) σ⁻¹ :=
        Real.rpow_mul hs.le _ _
      _ ≤ Real.rpow (Real.exp 2) σ⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hs.le _) hentropy hinvσ
      _ ≤ Real.rpow A σ⁻¹ := by
        apply Real.rpow_le_rpow (Real.exp_pos 2).le
        · dsimp [A]
          nlinarith [Real.exp_pos 2]
        · exact hinvσ
      _ ≤ Real.rpow A p :=
        Real.rpow_le_rpow_of_exponent_le hA_one hp_invσ
  have hKF : K * Real.rpow s (-(2 * s / σ)) ≤ Real.rpow (A ^ 2) p := by
    calc
      K * Real.rpow s (-(2 * s / σ)) ≤
          Real.rpow A p * Real.rpow A p :=
        mul_le_mul hK_Ap hfactor (Real.rpow_nonneg hs.le _)
          (Real.rpow_nonneg (by linarith [hA_one]) _)
      _ = Real.rpow (A ^ 2) p := by
        rw [show A ^ 2 = A * A by ring]
        exact (Real.mul_rpow (by linarith [hA_one]) (by linarith [hA_one])).symm
  have hbase : 0 ≤ C₀ / σ := div_nonneg hC₀.le hσ.le
  calc
    K * (Real.rpow (C₀ / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
        Real.rpow s (-(2 * s / (1 - s - t)))) =
        (K * Real.rpow s (-(2 * s / σ))) * Real.rpow (C₀ / σ) p := by
      simp only [σ, p]
      ring
    _ ≤ Real.rpow (A ^ 2) p * Real.rpow (C₀ / σ) p :=
      mul_le_mul_of_nonneg_right hKF (Real.rpow_nonneg hbase _)
    _ = Real.rpow ((A ^ 2) * (C₀ / σ)) p := by
      exact (Real.mul_rpow (sq_nonneg A) hbase).symm
    _ = Real.rpow (((Real.exp 2 * K) ^ 2 * C₀) / (1 - s - t))
        (2 + 4 * s / (1 - s - t)) := by
      simp only [A, σ, p]
      congr 1
      ring

/-- Squared exact datum conversion, including the paper's leading
`sqrt(2t)` normalization and invariance under the equation-sign change. -/
theorem besov_neg_sq_le_paperFractionalFullNorm
    (d : ℕ) [NeZero d] {t : ℝ} (ht : 0 < t)
    (sF : FractionalOrder) (hsF : sF.1 = 2 * t)
    (F : CubeEuclideanWspField (originCube d 0) sF FiniteLpExponent.two) :
    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d 0) (2 * t)
        (fun x => -F.toField x) ^ 2 ≤
      caccioppoliExactDatumConstant d ^ 2 * Real.rpow (2 * t) (-1 : ℝ) *
        (paperFractionalFullNorm (originCube d 0) sF FiniteLpExponent.two
          F.toField).toReal ^ 2 := by
  let G := negCubeEuclideanWspField F
  let S : ℝ≥0∞ := cubeEuclideanWspESeminorm (originCube d 0) sF
    FiniteLpExponent.two F.toField
  let N : ℝ≥0∞ := paperFractionalFullNorm (originCube d 0) sF
    FiniteLpExponent.two F.toField
  have hB := scaleNormalizedPositiveBesovVectorSeminormTwo_le_exactDatum d sF G
  rw [negCubeEuclideanWspField_toField, hsF,
    cubeEuclideanWspESeminorm_neg] at hB
  have hSfull := cubeEuclideanWspESeminorm_le_fullENorm
    (originCube d 0) sF FiniteLpExponent.two F.toField
  have hfullN := cubeEuclideanWspFullENorm_le_paperFractionalFullNorm
    (originCube d 0) sF FiniteLpExponent.two F.toField
  have hNtop : N ≠ ∞ := by
    dsimp [N, paperFractionalFullNorm, paperFractionalSeminorm]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
          ENNReal.ofReal_ne_top)
        F.eSeminorm_lt_top.ne
    · exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_ne_zero
          (ENNReal.ofReal_ne_zero_iff.mpr (cubeScaleFactor_pos' (originCube d 0)))
          ENNReal.ofReal_ne_top)
        F.normalizedEuclideanLpENorm_lt_top.ne
  have hfactorTop : (ENNReal.ofReal sF.1) ^
      (-(FiniteLpExponent.two.exponent.toReal)⁻¹) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr sF.2.1)
      ENNReal.ofReal_ne_top
  have hrealFull := ENNReal.toReal_mono (ENNReal.mul_ne_top hfactorTop hNtop) hfullN
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal sF.2.1.le] at hrealFull
  norm_num at hrealFull
  have hS : S.toReal ≤ Real.rpow (2 * t) (-(1 / 2 : ℝ)) * N.toReal := by
    calc
      S.toReal ≤ (cubeEuclideanWspFullENorm (originCube d 0) sF
          FiniteLpExponent.two F.toField).toReal := by
        exact ENNReal.toReal_mono F.fullENorm_lt_top.ne hSfull
      _ ≤ Real.rpow sF.1 (-(1 / 2 : ℝ)) * N.toReal := hrealFull
      _ = Real.rpow (2 * t) (-(1 / 2 : ℝ)) * N.toReal := by rw [hsF]
  have hD : 0 ≤ caccioppoliExactDatumConstant d :=
    (caccioppoliExactDatumConstant_pos d).le
  have hBnonneg : 0 ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d 0) (2 * t)
        (fun x => -F.toField x) := by
    simpa [G, hsF] using
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        ((cubeEuclideanWspField_forceSobolevRegularity sF G).toForceBesovRegularity
          sF.2.1 sF.2.2.le)
  have hfront : 0 ≤ Real.rpow (2 * t) (-(1 / 2 : ℝ)) * N.toReal := by
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) ENNReal.toReal_nonneg
  have hBpaper :
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d 0) (2 * t)
          (fun x => -F.toField x) ≤
        caccioppoliExactDatumConstant d *
          (Real.rpow (2 * t) (-(1 / 2 : ℝ)) * N.toReal) :=
    hB.trans (mul_le_mul_of_nonneg_left hS hD)
  have hpow : (Real.rpow (2 * t) (-(1 / 2 : ℝ))) ^ 2 =
      Real.rpow (2 * t) (-1 : ℝ) := by
    calc
      (Real.rpow (2 * t) (-(1 / 2 : ℝ))) ^ 2 =
          Real.rpow (Real.rpow (2 * t) (-(1 / 2 : ℝ))) (2 : ℝ) :=
        (Real.rpow_two _).symm
      _ = Real.rpow (2 * t) ((-(1 / 2 : ℝ)) * 2) :=
        (Real.rpow_mul (by positivity) _ _).symm
      _ = Real.rpow (2 * t) (-1 : ℝ) := by norm_num
  calc
    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d 0) (2 * t)
        (fun x => -F.toField x) ^ 2 ≤
      (caccioppoliExactDatumConstant d *
        (Real.rpow (2 * t) (-(1 / 2 : ℝ)) * N.toReal)) ^ 2 :=
      (sq_le_sq₀ hBnonneg (mul_nonneg hD hfront)).mpr hBpaper
    _ = caccioppoliExactDatumConstant d ^ 2 * Real.rpow (2 * t) (-1 : ℝ) *
        N.toReal ^ 2 := by rw [mul_pow, mul_pow, hpow]; ring

/-! ## Interior datum

PROVENANCE: the next construction mirrors
`Algsuperdiff/Section4/Provider/ExcessDecay/CaccioppoliInteriorDatum.lean`.
The proof is repeated here because GMC cannot import the separate
Superdiffusion repository. -/

/-- In the interior regime every `H¹` function has the localized zero trace
required by the boundary-patch carrier. -/
theorem localizedZeroTraceFunctionOn_of_patch_subset {d : ℕ}
    {U V : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {u : Vec d → ℝ} (hu : MemH1 U u) :
    Ch01.LocalizedZeroTraceFunctionOn U V u := by
  intro eta heta heta_compact heta_sub
  exact memH10_mul_of_contDiff_hasCompactSupport hU heta heta_compact
    (heta_sub.trans hVU) hu

/-- A cube window contains its centre. -/
theorem mem_openCubeAtScale_center {d : ℕ} (x : Vec d) (m : ℤ) :
    x ∈ openCubeAtScale x m := by
  intro i
  have h3 : 0 < Real.rpow (3 : ℝ) ((m : ℤ) : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  simp only [sub_self, abs_zero]
  linarith only [h3]

/-- A real-centred cube at the scale and centre of a triadic cube is its open
cube set. -/
theorem openCubeAtScale_cubeCenter {d : ℕ} (Q : TriadicCube d) :
    openCubeAtScale (cubeCenter Q) Q.scale = openCubeSet Q := by
  rw [← ball_cubeCenter_eq_openCubeSet Q]
  rw [ball_pi (cubeCenter Q) (cubeRadius_pos Q)]
  ext x
  simp only [openCubeAtScale, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    true_implies, Real.ball_eq_Ioo, cubeRadius, cubeScaleFactor]
  have hhalf : Real.rpow (3 : ℝ) ((Q.scale : ℤ) : ℝ) / 2 =
      (1 / 2 : ℝ) * Real.rpow 3 ((Q.scale : ℤ) : ℝ) := by ring
  have hpow : Real.rpow (3 : ℝ) ((Q.scale : ℤ) : ℝ) =
      (3 : ℝ) ^ Q.scale := Real.rpow_intCast 3 Q.scale
  constructor
  · intro hx i
    have hi := hx i
    rw [abs_lt] at hi
    constructor <;> linarith only [hi.1, hi.2, hhalf, hpow]
  · intro hx i
    have hi := hx i
    rw [abs_lt]
    constructor <;> linarith only [hi.1, hi.2, hhalf, hpow]

/-- If a centre lies in `□_(n+1)`, every cube of scale at most `n+1`
centred there lies in `□_(n+2)`.  This is the fixed-cover geometry used in
the source proof. -/
theorem openCubeAtScale_subset_origin_succ_succ {d : ℕ} {k n : ℤ}
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (n + 1)))
    (hk : k ≤ n + 1) :
    openCubeAtScale x k ⊆ openCubeSet (originCube d (n + 2)) := by
  have hstep : (3 : ℝ) ^ (n + 2) = 3 ^ (n + 1) * 3 := by
    have hn : n + 2 = n + 1 + 1 := by ring
    rw [hn, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hk3 : (3 : ℝ) ^ k ≤ 3 ^ (n + 1) :=
    zpow_le_zpow_right₀ (by norm_num) hk
  have hpos : 0 < (3 : ℝ) ^ (n + 1) := zpow_pos (by norm_num) _
  intro y hy
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hxi := hx i
  have hyi := hy i
  change |y i - x i| < Real.rpow 3 ((k : ℤ) : ℝ) / 2 at hyi
  have hpowk : Real.rpow (3 : ℝ) ((k : ℤ) : ℝ) =
      (3 : ℝ) ^ k := Real.rpow_intCast 3 k
  rw [hstep]
  rw [abs_lt] at hyi
  constructor <;>
    linarith only [hxi.1, hxi.2, hyi.1, hyi.2, hk3, hpos, hpowk]

/-- Origin cubes are nested with their scale. -/
theorem openCubeSet_originCube_subset_of_scale_le {d : ℕ} {k l : ℤ}
    (hkl : k ≤ l) :
    openCubeSet (originCube d k) ⊆ openCubeSet (originCube d l) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hpow : (3 : ℝ) ^ k ≤ 3 ^ l := zpow_le_zpow_right₀ (by norm_num) hkl
  exact ⟨by linarith only [(hx i).1, hpow],
    by linarith only [(hx i).2, hpow]⟩

/-- An interior core whose small window is already contained in the parent is
exactly that window. -/
theorem caccioppoliCoreSet_eq_openCubeAtScale {d : ℕ}
    {Q : TriadicCube d} {x : Vec d}
    (hx : openCubeAtScale x (Q.scale - 2) ⊆ openCubeSet Q) :
    caccioppoliCoreSet Q x = openCubeAtScale x (Q.scale - 2) := by
  exact Set.inter_eq_right.mpr hx




theorem integrableOn_coefficientEnergyDensity_coeffOn {d : ℕ}
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) :
    MeasureTheory.IntegrableOn (coefficientEnergyDensity a.toCoeffField u.grad)
      (openCubeSet Q) := by
  let b : Ch02.CoeffOn (Ch02.cubeDomain Q) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Ch02.cubeDomain Q) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet Q) b.toCoeffField := by
    simpa only [b, Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
        (Ch02.cubeDomain Q) a
  have hB : MeasureTheory.IntegrableOn
      (coefficientEnergyDensity b.toCoeffField u.grad) (openCubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      u.grad_memVectorL2
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] a.toCoeffField := by
    simpa only [b, Ch02.cubeDomain_coe, Ch02.CoeffOn.AEEq] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Ch02.cubeDomain Q) a
  apply hB.congr
  filter_upwards [hba] with x hx
  simp only [coefficientEnergyDensity, hx]

theorem integrable_coefficientEnergyDensity_coeffOn_normalizedCubeMeasure
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) :
    MeasureTheory.Integrable (coefficientEnergyDensity a.toCoeffField u.grad)
      (normalizedCubeMeasure Q) := by
  have hA : MeasureTheory.IntegrableOn
      (coefficientEnergyDensity a.toCoeffField u.grad) (openCubeSet Q) := by
    exact integrableOn_coefficientEnergyDensity_coeffOn Q a u
  simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
    hA.smul_measure ENNReal.ofReal_ne_top

theorem ae_nonneg_coefficientEnergyDensity_coeffOn_normalizedCubeMeasure
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,
      0 ≤ coefficientEnergyDensity a.toCoeffField u.grad x := by
  let b : Ch02.CoeffOn (Ch02.cubeDomain Q) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Ch02.cubeDomain Q) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet Q) b.toCoeffField := by
    simpa only [b, Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
        (Ch02.cubeDomain Q) a
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] a.toCoeffField := by
    simpa only [b, Ch02.cubeDomain_coe, Ch02.CoeffOn.AEEq] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Ch02.cubeDomain Q) a
  have hnonneg : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      0 ≤ coefficientEnergyDensity a.toCoeffField u.grad x := by
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q), hba]
      with x hxQ hxa
    change 0 ≤ vecDot (u.grad x)
      (matVecMul (symmPart (a.toCoeffField x)) (u.grad x))
    rw [← hxa]
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll u.grad x hxQ
  simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
    MeasureTheory.Measure.ae_smul_measure hnonneg
      (ENNReal.ofReal ((cubeVolume Q)⁻¹))

theorem volumeAverage_openCubeSet_eq_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = cubeAverage Q f := by
  calc
    volumeAverage (openCubeSet Q) f =
        (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume := by
      unfold volumeAverage
      rw [volume_openCubeSet_toReal]
    _ = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂MeasureTheory.volume := by
      rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = cubeAverage Q f := rfl

/-- The interior specialization of the boundary-patch carrier. -/
def interiorForcedCaccioppoliDatum {d : ℕ} {Q : TriadicCube d}
    {a : CoeffFamily d} (x : Vec d) {g : Vec d → Vec d}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (hu : IsForcedEquation Q a u g)
    (hpatch : openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q) :
    BoundaryForcedCaccioppoliDatum Q a x g where
  toH1 := u
  weakSolution := hu
  zeroTraceOnBoundaryPatch := by
    refine localizedZeroTraceFunctionOn_of_patch_subset
      (by
        rw [Ch02.cubeDomain_coe]
        exact isOpenBoundedConvexDomain_openCubeSet Q)
      (by
        rw [Ch02.cubeDomain_coe]
        exact hpatch)
      ⟨u, rfl⟩

/-- The source-shaped boundary RHS after D-024 replaces the packaged pole by
the printed `t⁻¹¹` envelope. -/
noncomputable def boundaryCaccioppoliQuarterRHS {d : ℕ} (C : ℝ)
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    {g : Vec d → Vec d} (s t : ℝ)
    (u : BoundaryForcedCaccioppoliDatum Q a x g) : ℝ :=
  caccioppoliWithRHSPrefactor C Q a s t *
    (Ch02.lambdaS Q t a *
        Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
        boundaryForcedCaccioppoliParentL2Sq u +
      Real.rpow t (-11 : ℝ) *
        Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2)

/-- The D-024 scalar envelope for the pole-bearing forcing coefficient. -/
theorem rpow_neg_eight_div_one_sub_two_mul_le_two_mul_rpow_neg_eleven
    {t : ℝ} (ht : 0 < t) (ht_quarter : t ≤ 1 / 4) :
    Real.rpow t (-8 : ℝ) / (1 - 2 * t) ≤
      2 * Real.rpow t (-11 : ℝ) := by
  have ht_one : t ≤ 1 := ht_quarter.trans (by norm_num)
  have hden : (1 : ℝ) / 2 ≤ 1 - 2 * t := by
    linarith only [ht_quarter]
  have hden_pos : 0 < 1 - 2 * t := lt_of_lt_of_le (by norm_num) hden
  have hpow_nonneg : 0 ≤ Real.rpow t (-8 : ℝ) := Real.rpow_nonneg ht.le _
  have hdiv : Real.rpow t (-8 : ℝ) / (1 - 2 * t) ≤
      2 * Real.rpow t (-8 : ℝ) := by
    rw [div_le_iff₀ hden_pos]
    have hmul :
        2 * Real.rpow t (-8 : ℝ) * ((1 : ℝ) / 2) ≤
          2 * Real.rpow t (-8 : ℝ) * (1 - 2 * t) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    nlinarith only [hmul]
  have hpow : Real.rpow t (-8 : ℝ) ≤ Real.rpow t (-11 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge ht ht_one (by norm_num)
  exact hdiv.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))

/-- After inserting the paper's leading `sqrt(2t)` datum normalization, the
raw pole-bearing coefficient is bounded by the printed `t⁻¹¹` coefficient on
the D-024 range. -/
theorem rpow_neg_eight_div_one_sub_two_mul_two_t_inv_le_rpow_neg_eleven
    {t : ℝ} (ht : 0 < t) (ht_quarter : t ≤ 1 / 4) :
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
        Real.rpow (2 * t) (-1 : ℝ) ≤ Real.rpow t (-11 : ℝ) := by
  have ht_one : t ≤ 1 := ht_quarter.trans (by norm_num)
  have hden : (1 : ℝ) / 2 ≤ 1 - 2 * t := by
    linarith only [ht_quarter]
  have hden_pos : 0 < 1 - 2 * t := lt_of_lt_of_le (by norm_num) hden
  have hpow_nonneg : 0 ≤ Real.rpow t (-8 : ℝ) := Real.rpow_nonneg ht.le _
  have hdiv : Real.rpow t (-8 : ℝ) / (1 - 2 * t) ≤
      2 * Real.rpow t (-8 : ℝ) := by
    rw [div_le_iff₀ hden_pos]
    have hmul :
        2 * Real.rpow t (-8 : ℝ) * ((1 : ℝ) / 2) ≤
          2 * Real.rpow t (-8 : ℝ) * (1 - 2 * t) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    nlinarith only [hmul]
  have hnorm :
      2 * Real.rpow t (-8 : ℝ) * Real.rpow (2 * t) (-1 : ℝ) =
        Real.rpow t (-9 : ℝ) := by
    have hinv : Real.rpow (2 * t) (-1 : ℝ) = (2 * t)⁻¹ :=
      Real.rpow_neg_one (2 * t)
    rw [hinv]
    have htwo_t : (2 * t)⁻¹ = (1 / 2 : ℝ) * t⁻¹ := by
      field_simp [ht.ne']
    have htinv : t⁻¹ = Real.rpow t (-1 : ℝ) :=
      (Real.rpow_neg_one t).symm
    rw [htwo_t, htinv]
    calc
      2 * Real.rpow t (-8 : ℝ) *
          ((1 / 2 : ℝ) * Real.rpow t (-1 : ℝ)) =
        Real.rpow t (-8 : ℝ) * Real.rpow t (-1 : ℝ) := by ring
      _ = Real.rpow t ((-8 : ℝ) + (-1 : ℝ)) :=
        (Real.rpow_add ht (-8 : ℝ) (-1 : ℝ)).symm
      _ = Real.rpow t (-9 : ℝ) := by norm_num
  have hpow : Real.rpow t (-9 : ℝ) ≤ Real.rpow t (-11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht_one (by norm_num)
  calc
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
        Real.rpow (2 * t) (-1 : ℝ) ≤
      (2 * Real.rpow t (-8 : ℝ)) * Real.rpow (2 * t) (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg (by positivity) _)
    _ = Real.rpow t (-9 : ℝ) := hnorm
    _ ≤ Real.rpow t (-11 : ℝ) := hpow

/-- Below-surface form of `l.coarse.grained.Caccioppoli.RHS.ASD` on the
D-024 range.  The datum is CoarseGraining's boundary-patch/zero-trace carrier;
the later source-facing finite-cover theorem supplies this carrier on every
interior patch. -/
theorem exists_boundary_caccioppoli_quarter (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        {x : Vec d} {g : Vec d → Vec d}
        (u : BoundaryForcedCaccioppoliDatum Q a x g),
        0 < s → s < 1 → 0 < t → t ≤ 1 / 4 → s + t < 1 →
          x ∈ openCubeSet Q → ForceBesovRegularity Q (2 * t) g →
            boundaryForcedCaccioppoliCoreEnergy u ≤
              boundaryCaccioppoliQuarterRHS C s t u := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    (coarseCaccioppoliRHSTheory (d := d)).exists_constant
  let C : ℝ := 2 * C₀
  have hC : 0 < C := mul_pos (by norm_num) hC₀
  refine ⟨C, hC, ?_⟩
  intro Q a s t x g u hs hs_one ht ht_quarter hst hx hg
  have ht_half : t < 1 / 2 := by linarith only [ht_quarter]
  have hraw : boundaryForcedCaccioppoliCoreEnergy u ≤
      boundaryCaccioppoliWithRHSRHS C₀ s t u :=
    hbound u hs hs_one ht ht_half hst hx hg
  let P₀ : ℝ := caccioppoliWithRHSPrefactor C₀ Q a s t
  let P : ℝ := caccioppoliWithRHSPrefactor C Q a s t
  let A : ℝ :=
    Ch02.lambdaS Q t a *
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
      boundaryForcedCaccioppoliParentL2Sq u
  let B₀ : ℝ :=
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
  let B : ℝ :=
    Real.rpow t (-11 : ℝ) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
  have hlambda_pos : 0 < Ch02.lambdaS Q t a := by
    unfold Ch02.lambdaS
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num)
  have hA : 0 ≤ A := by
    have hlambda : 0 ≤ Ch02.lambdaS Q t a := by
      unfold Ch02.lambdaS
      exact (Ch02.lambdaSq_finite_pos Q a ht (by norm_num)).le
    exact mul_nonneg
      (mul_nonneg hlambda (Real.rpow_nonneg (by norm_num) _))
      (normalizedL2SqOnSet_nonneg (openCubeSet Q) u.toH1.toFun
        (measurableSet_openCubeSet Q))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Real.rpow_nonneg hlambda_pos.le _))
      (sq_nonneg _)
  have hB₀B : B₀ ≤ 2 * B := by
    dsimp [B₀, B]
    have hfactor :=
      rpow_neg_eight_div_one_sub_two_mul_le_two_mul_rpow_neg_eleven
        ht ht_quarter
    have hrest : 0 ≤
        Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2 := by
      exact mul_nonneg (Real.rpow_nonneg hlambda_pos.le _) (sq_nonneg _)
    calc
      (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2 =
          (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
            (Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
              (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) := by
        ring
      _ ≤ (2 * Real.rpow t (-11 : ℝ)) *
            (Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
              (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) :=
        mul_le_mul_of_nonneg_right hfactor hrest
      _ = 2 *
          (Real.rpow t (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
            (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) := by
        ring
  have hsum : A + B₀ ≤ 2 * (A + B) := by
    calc
      A + B₀ ≤ A + 2 * B := add_le_add_right hB₀B A
      _ ≤ 2 * (A + B) := by nlinarith only [hA]
  have hP₀ : 0 ≤ P₀ := by
    dsimp [P₀]
    exact caccioppoliWithRHSPrefactor_nonneg hC₀.le hs ht hst
  have hscaled : P₀ * (A + B₀) ≤ 2 * P₀ * (A + B) := by
    calc
      P₀ * (A + B₀) ≤ P₀ * (2 * (A + B)) :=
        mul_le_mul_of_nonneg_left hsum hP₀
      _ = 2 * P₀ * (A + B) := by ring
  have hP : 2 * P₀ ≤ P := by
    dsimp [P₀, P, C]
    exact caccioppoliWithRHSPrefactor_mul_const_le_of_mul_constant_le
      (by norm_num) hC₀.le (le_refl (2 * C₀)) hs ht hst
  have hsum_nonneg : 0 ≤ A + B := add_nonneg hA hB
  calc
    boundaryForcedCaccioppoliCoreEnergy u ≤
        boundaryCaccioppoliWithRHSRHS C₀ s t u := hraw
    _ = P₀ * (A + B₀) := rfl
    _ ≤ 2 * P₀ * (A + B) := hscaled
    _ ≤ P * (A + B) := mul_le_mul_of_nonneg_right hP hsum_nonneg
    _ = boundaryCaccioppoliQuarterRHS C s t u := rfl

/-- Interior form of the below-surface D-024 estimate.  The sole geometric
hypothesis says that the boundary patch does not meet the parent boundary. -/
theorem exists_interior_caccioppoli_quarter (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        {x : Vec d} {g : Vec d → Vec d}
        (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))),
        IsForcedEquation Q a u g →
        0 < s → s < 1 → 0 < t → t ≤ 1 / 4 → s + t < 1 →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        ForceBesovRegularity Q (2 * t) g →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            caccioppoliWithRHSPrefactor C Q a s t *
              (Ch02.lambdaS Q t a *
                  Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                  normalizedL2SqOnSet (openCubeSet Q) u.toFun +
                Real.rpow t (-11 : ℝ) *
                  Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_boundary_caccioppoli_quarter d
  refine ⟨C, hC, ?_⟩
  intro Q a s t x g u hu hs hs_one ht ht_quarter hst hpatch hg
  have hx : x ∈ openCubeSet Q :=
    hpatch (mem_openCubeAtScale_center x (Q.scale - 1))
  have hmain := hbound (interiorForcedCaccioppoliDatum x u hu hpatch)
    hs hs_one ht ht_quarter hst hx hg
  simpa [boundaryForcedCaccioppoliCoreEnergy, boundaryCaccioppoliQuarterRHS,
    boundaryForcedCaccioppoliParentL2Sq, interiorForcedCaccioppoliDatum] using! hmain

/-! ## The fixed central-cube cover -/

/-- The source proof's finite-cover step, still expressed in the packaged
positive-Besov carrier.  All local estimates have the same right-hand side,
so normalized averaging over the `3^d` children introduces no extra factor. -/
theorem exists_originCube_caccioppoli_quarter_besov (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s t : ℝ), 0 < s → s < 1 → 0 < t → t ≤ 1 / 4 → s + t < 1 →
        ∀ (a : Ch02.TriadicCoeffFamily d)
          (u : H1Function (openCubeSet (originCube d 0)))
          (g : Vec d → Vec d),
          IsForcedEquation (originCube d 0) a u g →
          ForceBesovRegularity (originCube d 0) (2 * t) g →
            coefficientEnergyNorm (originCube d (-1)) a u.grad ^ 2 ≤
              caccioppoliWithRHSPrefactor C (originCube d 0) a s t *
                (Ch02.lambdaS (originCube d 0) t a *
                    cubeLpNorm (originCube d 0) (2 : ℝ≥0∞) u.toFun ^ 2 +
                  Real.rpow t (-11 : ℝ) *
                    Real.rpow (Ch02.lambdaS (originCube d 0) t a) (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo
                      (originCube d 0) (2 * t) g ^ 2) := by
  obtain ⟨C, hC, hlocal⟩ := exists_interior_caccioppoli_quarter d
  refine ⟨C, hC, ?_⟩
  intro s t hs hs_one ht ht_quarter hst a u g hu hg
  let Q₀ : TriadicCube d := originCube d 0
  let Q₁ : TriadicCube d := originCube d (-1)
  have hQ₁Q₀ : openCubeSet Q₁ ⊆ openCubeSet Q₀ := by
    simpa [Q₀, Q₁] using
      (openCubeSet_originCube_subset_of_scale_le (d := d)
        (k := (-1 : ℤ)) (l := 0) (by norm_num))
  let u₁ : H1Function (openCubeSet Q₁) :=
    u.restrict (isOpen_openCubeSet Q₁) (by simpa [Q₀] using hQ₁Q₀)
  let energy : Vec d → ℝ :=
    coefficientEnergyDensity (a.coeffOn Q₁).toCoeffField u₁.grad
  let B : ℝ :=
    caccioppoliWithRHSPrefactor C Q₀ a s t *
      (Ch02.lambdaS Q₀ t a * cubeLpNorm Q₀ (2 : ℝ≥0∞) u.toFun ^ 2 +
        Real.rpow t (-11 : ℝ) * Real.rpow (Ch02.lambdaS Q₀ t a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q₀ (2 * t) g ^ 2)
  have hint_open : MeasureTheory.IntegrableOn energy (openCubeSet Q₁) := by
    simpa [energy] using
      integrableOn_coefficientEnergyDensity_coeffOn Q₁ (a.coeffOn Q₁) u₁
  have hint_cube : MeasureTheory.IntegrableOn energy (cubeSet Q₁) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hint_open
  have hpartition : cubeAverage Q₁ energy =
      descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) :=
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q₁ 1 energy hint_cube
  have hchildren : ∀ R ∈ descendantsAtDepth Q₁ 1, cubeAverage R energy ≤ B := by
    intro R hR
    have hRscale : R.scale = -2 := by
      have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
      simpa [Q₁, originCube] using! hscale
    have hxQ₁ : cubeCenter R ∈ openCubeSet Q₁ :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR (cubeCenter_mem_openCubeSet R)
    have hpatch : openCubeAtScale (cubeCenter R) (Q₀.scale - 1) ⊆
        openCubeSet Q₀ := by
      have hgeom := openCubeAtScale_subset_origin_succ_succ
        (d := d) (k := -1) (n := -2) (x := cubeCenter R)
        (by simpa [Q₁] using hxQ₁) (by norm_num)
      simpa [Q₀, originCube] using! hgeom
    have hsmall : openCubeAtScale (cubeCenter R) (Q₀.scale - 2) ⊆
        openCubeSet Q₀ := by
      have hgeom := openCubeAtScale_subset_origin_succ_succ
        (d := d) (k := -2) (n := -2) (x := cubeCenter R)
        (by simpa [Q₁] using hxQ₁) (by norm_num)
      simpa [Q₀, originCube] using! hgeom
    have hcore : caccioppoliCoreSet Q₀ (cubeCenter R) = openCubeSet R := by
      rw [caccioppoliCoreSet_eq_openCubeAtScale hsmall]
      have hscaleQ₀ : Q₀.scale - 2 = R.scale := by
        change 0 - 2 = R.scale
        omega
      rw [hscaleQ₀, openCubeAtScale_cubeCenter]
    have hloc := hlocal (Q := Q₀) (a := a) (s := s) (t := t)
      (x := cubeCenter R) (g := g) u hu hs hs_one ht ht_quarter hst hpatch hg
    have hrestrict : Ch02.CoeffOn.RestrictsTo (a.coeffOn Q₀) (a.coeffOn Q₁) :=
      a.restrictsTo_of_subset hQ₁Q₀
    have hcoeffR : (a.coeffOn Q₁).toCoeffField
        =ᵐ[MeasureTheory.volume.restrict (cubeSet R)]
          (a.coeffOn Q₀).toCoeffField :=
      ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hrestrict
    have henergyR : energy =ᵐ[MeasureTheory.volume.restrict (cubeSet R)]
        coefficientEnergyDensity (a.coeffOn Q₀).toCoeffField u.grad := by
      filter_upwards [hcoeffR] with x hx
      simp [energy, u₁, H1Function.restrict, coefficientEnergyDensity, hx]
    have havg : cubeAverage R energy =
        cubeAverage R (coefficientEnergyDensity (a.coeffOn Q₀).toCoeffField u.grad) :=
      cubeAverage_eq_of_ae_eq_on_cubeSet henergyR
    rw [hcore] at hloc
    unfold localizedCoeffEnergyValue normalizedSetAverage at hloc
    rw [volumeAverage_openCubeSet_eq_cubeAverage] at hloc
    rw [havg]
    rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq
      Q₀ u.toFun u.memL2_normalizedCubeMeasure] at hloc
    change cubeAverage R
      (coefficientEnergyDensity (a.coeffOn Q₀).toCoeffField u.grad) ≤ _ at hloc
    have hQ₀scale : Q₀.scale = 0 := rfl
    rw [hQ₀scale] at hloc
    norm_num at hloc
    simpa [B, Q₀] using hloc
  have havg_le : descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) ≤ B := by
    calc
      descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) ≤
          descendantsAverage Q₁ 1 (fun _ => B) :=
        descendantsAverage_le_descendantsAverage Q₁ 1 hchildren
      _ = B := descendantsAverage_const Q₁ 1 B
  have henergy_nonneg : 0 ≤ ∫ x, energy x ∂normalizedCubeMeasure Q₁ := by
    exact MeasureTheory.integral_nonneg_of_ae
      (by
        simpa [energy, Pi.zero_def] using!
          ae_nonneg_coefficientEnergyDensity_coeffOn_normalizedCubeMeasure
            Q₁ (a.coeffOn Q₁) u₁)
  have hnorm : coefficientEnergyNorm Q₁ a u.grad ^ 2 = cubeAverage Q₁ energy := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    unfold coefficientEnergyNorm
    have hint_eq :
        (∫ x, vecDot (u.grad x)
            (matVecMul ((a.coeffOn Q₁).toCoeffField x) (u.grad x))
            ∂normalizedCubeMeasure Q₁) =
          ∫ x, energy x ∂normalizedCubeMeasure Q₁ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simpa [energy, u₁, H1Function.restrict] using
        (coefficientEnergyDensity_eq_unsymmetrized
          (a.coeffOn Q₁).toCoeffField u.grad x).symm
    rw [hint_eq, Real.sq_sqrt henergy_nonneg]
  calc
    coefficientEnergyNorm (originCube d (-1)) a u.grad ^ 2 =
        cubeAverage Q₁ energy := by simpa [Q₁] using hnorm
    _ = descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) := hpartition
    _ ≤ B := havg_le
    _ = _ := by simp [B, Q₀]

/-! ## Raw finite-cover form

The source-facing conversion below must retain the packaged coefficient until
after the paper's `sqrt(2t)` normalization is inserted.  Spending the D-024
slack earlier would lose one additional power of `t`. -/

theorem exists_interior_caccioppoli_raw (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        {x : Vec d} {g : Vec d → Vec d}
        (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))),
        IsForcedEquation Q a u g →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        ForceBesovRegularity Q (2 * t) g →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            caccioppoliWithRHSPrefactor C Q a s t *
              (Ch02.lambdaS Q t a *
                  Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                  normalizedL2SqOnSet (openCubeSet Q) u.toFun +
                (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
                  Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    (coarseCaccioppoliRHSTheory (d := d)).exists_constant
  refine ⟨C, hC, ?_⟩
  intro Q a s t x g u hu hs hs_one ht ht_half hst hpatch hg
  have hx : x ∈ openCubeSet Q :=
    hpatch (mem_openCubeAtScale_center x (Q.scale - 1))
  have hmain := hbound (interiorForcedCaccioppoliDatum x u hu hpatch)
    hs hs_one ht ht_half hst hx hg
  simpa [boundaryForcedCaccioppoliCoreEnergy, boundaryCaccioppoliWithRHSRHS,
    boundaryForcedCaccioppoliParentL2Sq, interiorForcedCaccioppoliDatum] using! hmain

/-- The raw fixed cover, retaining `t⁻⁸/(1-2t)` for the final exact-norm
conversion. -/
theorem exists_originCube_caccioppoli_raw_besov (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s t : ℝ), 0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        ∀ (a : Ch02.TriadicCoeffFamily d)
          (u : H1Function (openCubeSet (originCube d 0)))
          (g : Vec d → Vec d),
          IsForcedEquation (originCube d 0) a u g →
          ForceBesovRegularity (originCube d 0) (2 * t) g →
            coefficientEnergyNorm (originCube d (-1)) a u.grad ^ 2 ≤
              caccioppoliWithRHSPrefactor C (originCube d 0) a s t *
                (Ch02.lambdaS (originCube d 0) t a *
                    cubeLpNorm (originCube d 0) (2 : ℝ≥0∞) u.toFun ^ 2 +
                  (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
                    Real.rpow (Ch02.lambdaS (originCube d 0) t a) (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo
                      (originCube d 0) (2 * t) g ^ 2) := by
  obtain ⟨C, hC, hlocal⟩ := exists_interior_caccioppoli_raw d
  refine ⟨C, hC, ?_⟩
  intro s t hs hs_one ht ht_half hst a u g hu hg
  let Q₀ : TriadicCube d := originCube d 0
  let Q₁ : TriadicCube d := originCube d (-1)
  have hQ₁Q₀ : openCubeSet Q₁ ⊆ openCubeSet Q₀ := by
    simpa [Q₀, Q₁] using
      (openCubeSet_originCube_subset_of_scale_le (d := d)
        (k := (-1 : ℤ)) (l := 0) (by norm_num))
  let u₁ : H1Function (openCubeSet Q₁) :=
    u.restrict (isOpen_openCubeSet Q₁) (by simpa [Q₀] using hQ₁Q₀)
  let energy : Vec d → ℝ :=
    coefficientEnergyDensity (a.coeffOn Q₁).toCoeffField u₁.grad
  let B : ℝ :=
    caccioppoliWithRHSPrefactor C Q₀ a s t *
      (Ch02.lambdaS Q₀ t a * cubeLpNorm Q₀ (2 : ℝ≥0∞) u.toFun ^ 2 +
        (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow (Ch02.lambdaS Q₀ t a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q₀ (2 * t) g ^ 2)
  have hint_open : MeasureTheory.IntegrableOn energy (openCubeSet Q₁) := by
    simpa [energy] using
      integrableOn_coefficientEnergyDensity_coeffOn Q₁ (a.coeffOn Q₁) u₁
  have hint_cube : MeasureTheory.IntegrableOn energy (cubeSet Q₁) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hint_open
  have hpartition : cubeAverage Q₁ energy =
      descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) :=
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q₁ 1 energy hint_cube
  have hchildren : ∀ R ∈ descendantsAtDepth Q₁ 1, cubeAverage R energy ≤ B := by
    intro R hR
    have hRscale : R.scale = -2 := by
      have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
      simpa [Q₁, originCube] using! hscale
    have hxQ₁ : cubeCenter R ∈ openCubeSet Q₁ :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR (cubeCenter_mem_openCubeSet R)
    have hpatch : openCubeAtScale (cubeCenter R) (Q₀.scale - 1) ⊆
        openCubeSet Q₀ := by
      have hgeom := openCubeAtScale_subset_origin_succ_succ
        (d := d) (k := -1) (n := -2) (x := cubeCenter R)
        (by simpa [Q₁] using hxQ₁) (by norm_num)
      simpa [Q₀, originCube] using! hgeom
    have hsmall : openCubeAtScale (cubeCenter R) (Q₀.scale - 2) ⊆
        openCubeSet Q₀ := by
      have hgeom := openCubeAtScale_subset_origin_succ_succ
        (d := d) (k := -2) (n := -2) (x := cubeCenter R)
        (by simpa [Q₁] using hxQ₁) (by norm_num)
      simpa [Q₀, originCube] using! hgeom
    have hcore : caccioppoliCoreSet Q₀ (cubeCenter R) = openCubeSet R := by
      rw [caccioppoliCoreSet_eq_openCubeAtScale hsmall]
      have hscaleQ₀ : Q₀.scale - 2 = R.scale := by
        change 0 - 2 = R.scale
        omega
      rw [hscaleQ₀, openCubeAtScale_cubeCenter]
    have hloc := hlocal (Q := Q₀) (a := a) (s := s) (t := t)
      (x := cubeCenter R) (g := g) u hu hs hs_one ht ht_half hst hpatch hg
    have hrestrict : Ch02.CoeffOn.RestrictsTo (a.coeffOn Q₀) (a.coeffOn Q₁) :=
      a.restrictsTo_of_subset hQ₁Q₀
    have hcoeffR : (a.coeffOn Q₁).toCoeffField
        =ᵐ[MeasureTheory.volume.restrict (cubeSet R)]
          (a.coeffOn Q₀).toCoeffField :=
      ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hrestrict
    have henergyR : energy =ᵐ[MeasureTheory.volume.restrict (cubeSet R)]
        coefficientEnergyDensity (a.coeffOn Q₀).toCoeffField u.grad := by
      filter_upwards [hcoeffR] with x hx
      simp [energy, u₁, H1Function.restrict, coefficientEnergyDensity, hx]
    have havg : cubeAverage R energy =
        cubeAverage R (coefficientEnergyDensity (a.coeffOn Q₀).toCoeffField u.grad) :=
      cubeAverage_eq_of_ae_eq_on_cubeSet henergyR
    rw [hcore] at hloc
    unfold localizedCoeffEnergyValue normalizedSetAverage at hloc
    rw [volumeAverage_openCubeSet_eq_cubeAverage] at hloc
    rw [havg]
    rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq
      Q₀ u.toFun u.memL2_normalizedCubeMeasure] at hloc
    change cubeAverage R
      (coefficientEnergyDensity (a.coeffOn Q₀).toCoeffField u.grad) ≤ _ at hloc
    have hQ₀scale : Q₀.scale = 0 := rfl
    rw [hQ₀scale] at hloc
    norm_num at hloc
    simpa [boundaryCaccioppoliWithRHSRHS, B, Q₀] using hloc
  have havg_le : descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) ≤ B := by
    calc
      descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) ≤
          descendantsAverage Q₁ 1 (fun _ => B) :=
        descendantsAverage_le_descendantsAverage Q₁ 1 hchildren
      _ = B := descendantsAverage_const Q₁ 1 B
  have henergy_nonneg : 0 ≤ ∫ x, energy x ∂normalizedCubeMeasure Q₁ := by
    exact MeasureTheory.integral_nonneg_of_ae
      (by
        simpa [energy, Pi.zero_def] using!
          ae_nonneg_coefficientEnergyDensity_coeffOn_normalizedCubeMeasure
            Q₁ (a.coeffOn Q₁) u₁)
  have hnorm : coefficientEnergyNorm Q₁ a u.grad ^ 2 = cubeAverage Q₁ energy := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    unfold coefficientEnergyNorm
    have hint_eq :
        (∫ x, vecDot (u.grad x)
            (matVecMul ((a.coeffOn Q₁).toCoeffField x) (u.grad x))
            ∂normalizedCubeMeasure Q₁) =
          ∫ x, energy x ∂normalizedCubeMeasure Q₁ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simpa [energy, u₁, H1Function.restrict] using
        (coefficientEnergyDensity_eq_unsymmetrized
          (a.coeffOn Q₁).toCoeffField u.grad x).symm
    rw [hint_eq, Real.sq_sqrt henergy_nonneg]
  calc
    coefficientEnergyNorm (originCube d (-1)) a u.grad ^ 2 =
        cubeAverage Q₁ energy := by simpa [Q₁] using hnorm
    _ = descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) := hpartition
    _ ≤ B := havg_le
    _ = _ := by simp [B, Q₀]

end

end SubdiffusiveProcess.CoarseGrainingVocab
