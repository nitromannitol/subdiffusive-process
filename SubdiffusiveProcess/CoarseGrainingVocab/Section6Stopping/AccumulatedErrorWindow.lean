module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorResponseWindow

@[expose] public section

/-!
# Fixed-parameter accumulated-error window

This module composes the three literal rearrangements in `l.sum.the.errors`:
the annular response triangle, the finite shell-field triangle, and the
infinite gradient suffix.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

theorem isBigO_comp_translatePotentialSample {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    {X : Sample d → ℝ} {A σ : ℝ}
    (hX : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma σ) X A) :
    IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma σ)
      (fun omega ↦ X (translatePotentialSample z omega)) A := by
  intro t ht
  have hset : IndependentSums.upperTailEvent
      (fun omega ↦ |X (translatePotentialSample z omega)|) (A * t) =
      translatePotentialSample z ⁻¹'
        IndependentSums.upperTailEvent (fun omega ↦ |X omega|) (A * t) := rfl
  rw [hset]
  have hmeasure := Section6Covariance.measure_preimage_translatePotentialSample
    M z (IndependentSums.upperTailEvent (fun omega ↦ |X omega|) (A * t))
  rw [Measure.real, hmeasure]
  exact hX ht

theorem isBigO_add_gammaTwo {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {X Y : Sample d → ℝ} {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hX : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X A)
    (hY : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) Y B)
    (hXm : AEMeasurable X M.P.toMeasure)
    (hYm : AEMeasurable Y M.P.toMeasure) :
    IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) (fun omega ↦ X omega + Y omega)
      (Ch04.gammaTriangleConst 2 * (A + B)) := by
  let Z : Bool → Sample d → ℝ := fun b ↦ if b then X else Y
  let a : Bool → ℝ := fun b ↦ if b then A else B
  have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma_aemeasurable
    (μ := M.P.toMeasure) ({false, true} : Finset Bool)
    (X := Z) (a := a) (σ := 2) (by norm_num) (by simp)
    (fun b hb ↦ by cases b <;> simp [a, hA, hB])
    (fun b hb ↦ by
      cases b
      · simpa [Z, a] using! hY
      · simpa [Z, a] using! hX)
    (fun b ↦ by
      cases b
      · simpa [Z] using! hYm
      · simpa [Z] using! hXm)
  simpa [Z, a, add_comm] using! hsum

theorem measurable_accumulatedResponseLowRows {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) :
    Measurable (accumulatedResponseLowRows M n) := by
  unfold accumulatedResponseLowRows
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul (measurable_holderResponseRow M j)

theorem measurable_accumulatedFiniteFieldLowWindow {d : ℕ}
    (z : Vec d) (s : ℝ) (n m : ℕ) :
    Measurable (accumulatedFiniteFieldLowWindow z s n m) := by
  unfold accumulatedFiniteFieldLowWindow
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_accumulatedFiniteFieldColumn_shellSigma z s n m i).mono
    (shellSigma_le i) le_rfl

theorem measurable_centeredAccumulatedFiniteFieldActiveWindow {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : Vec d) (s : ℝ) (n m : ℕ) :
    Measurable (centeredAccumulatedFiniteFieldActiveWindow M z s n m) := by
  unfold centeredAccumulatedFiniteFieldActiveWindow
  apply Finset.measurable_sum
  intro i hi
  exact measurable_centeredAccumulatedFiniteFieldColumn M z s n m i

theorem measurable_centeredAccumulatedGradientWindow {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d) (n m : ℕ) :
    Measurable (centeredAccumulatedGradientWindow M z n m) := by
  unfold centeredAccumulatedGradientWindow
  apply Finset.measurable_sum
  intro k hk
  exact measurable_centeredAccumulatedGradientOwnRow M k z

theorem aemeasurable_accumulatedGradientEnvelope {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (z : Vec d) :
    AEMeasurable (accumulatedGradientEnvelope (d := d) k z)
      M.P.toMeasure := by
  let F : ℕ → Sample d → ℝ := fun N omega ↦
    (d : ℝ) * ∑ q ∈ Finset.range N, accumulatedGradientLayer k q z omega
  apply aemeasurable_of_tendsto_metrizable_ae'
    (f := F) (g := accumulatedGradientEnvelope k z)
  · intro N
    exact (measurable_const.mul (Finset.measurable_sum _ fun q _ ↦
      measurable_accumulatedGradientLayer k q z)).aemeasurable
  · filter_upwards [ae_summable_accumulatedGradientLayer M k z]
      with omega hsum
    unfold F accumulatedGradientEnvelope
    exact (hsum.hasSum.tendsto_sum_nat.const_mul (d : ℝ))

theorem accumulatedGradientEnvelope_nonneg {d : ℕ}
    (k : ℕ) (z : Vec d) (omega : Sample d) :
    0 ≤ accumulatedGradientEnvelope k z omega := by
  unfold accumulatedGradientEnvelope
  exact mul_nonneg (Nat.cast_nonneg d)
    (tsum_nonneg fun q ↦ accumulatedGradientLayer_nonneg k q z omega)

theorem accumulatedError_none_holderStoppingS_eq_parts {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (z : Vec d)
    (omega : Sample d) :
    accumulatedError M none k z holderStoppingS omega =
      translatedAccumulatedResponseSup M k z omega +
        translatedAccumulatedBlockSup k z holderStoppingS omega +
        (3 : ℝ) ^ (-(holderStoppingS / 8) * k) *
          supNormOn (translatedCube d (k : ℤ) z) (omega 0) +
        ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0 := by
  unfold accumulatedError translatedAccumulatedResponseSup
    translatedAccumulatedBlockSup
  simp only [Option.getD_none, min_self]



theorem ae_sum_accumulatedError_le_carriers {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M none k z holderStoppingS omega) ≤
        2 * (accumulatedResponseLowWindow M n m
              (translatePotentialSample z omega) +
            accumulatedResponseActiveWindow M n m
              (translatePotentialSample z omega)) +
        2 * (accumulatedFiniteFieldLowWindow z holderStoppingS n m omega +
            accumulatedFiniteFieldActiveWindow z holderStoppingS n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := by
  have hresponse0 := ae_sum_accumulatedResponseSup_le_windowConvolution M n m
  have hresponse :=
    (Section6Covariance.measurePreserving_translatePotentialSample M z).quasiMeasurePreserving.ae
      hresponse0
  filter_upwards [hresponse, ae_sum_accumulatedGradientSuffix_le M z hnm]
    with omega hresp hgrad
  have hfinite :=
    sum_translatedBlockSup_add_shellZero_le_finiteFieldWindowConvolution
      z holderStoppingS_pos n m omega
  have hrespEq := accumulatedResponseWindowConvolution_eq_low_add_active
    M hnm (translatePotentialSample z omega)
  have hfieldEq := accumulatedFiniteFieldWindowConvolution_eq_low_add_active
    z holderStoppingS hnm omega
  calc
    (∑ k ∈ Finset.Icc n m,
        accumulatedError M none k z holderStoppingS omega) =
      (∑ k ∈ Finset.Icc n m,
          translatedAccumulatedResponseSup M k z omega) +
        (∑ k ∈ Finset.Icc n m,
          (translatedAccumulatedBlockSup k z holderStoppingS omega +
            (3 : ℝ) ^ (-(holderStoppingS / 8) * k) *
              supNormOn (translatedCube d (k : ℤ) z) (omega 0))) +
        (∑ k ∈ Finset.Icc n m, ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0) := by
      simp_rw [accumulatedError_none_holderStoppingS_eq_parts]
      simp_rw [Finset.sum_add_distrib]
      ring
    _ ≤ 2 * accumulatedResponseWindowConvolution M n m
          (translatePotentialSample z omega) +
        2 * accumulatedFiniteFieldWindowConvolution z holderStoppingS n m omega +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := by
      have hresp' : (∑ k ∈ Finset.Icc n m,
          translatedAccumulatedResponseSup M k z omega) ≤
          2 * accumulatedResponseWindowConvolution M n m
            (translatePotentialSample z omega) := by
        simpa only [translatedAccumulatedResponseSup_eq_origin_translate]
          using! hresp
      linarith
    _ = _ := by rw [hrespEq, hfieldEq]

/-- Sum of the centered/short-memory carriers left after retaining the three
linear means. -/
noncomputable def accumulatedErrorWindowFluctuation {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    (n m : ℕ) : Sample d → ℝ :=
  fun omega ↦
    2 * (8 / holderStoppingS) *
      (accumulatedResponseLowRows M n (translatePotentialSample z omega) +
        centeredHolderResponseWindow M n m (translatePotentialSample z omega)) +
    2 * (accumulatedFiniteFieldLowWindow z holderStoppingS n m omega +
      centeredAccumulatedFiniteFieldActiveWindow M z holderStoppingS n m omega) +
    (3 / 2 : ℝ) *
      (centeredAccumulatedGradientWindow M z n m omega +
        accumulatedGradientEnvelope m z omega)

def accumulatedErrorWindowMeanBound {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (A : ℝ) (n m : ℕ) : ℝ :=
  ((m + 1 - n : ℕ) : ℝ) *
    (2 * (8 / holderStoppingS) * (IndependentSums.gammaMomentConst 2 * A) +
      2 * (IndependentSums.gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M holderStoppingS) +
      (3 / 2 : ℝ) *
        (IndependentSums.gammaMomentConst 2 * accumulatedGradientOwnRowScale M))

def accumulatedResponseActiveWindowScale (d : ℕ) (A : ℝ) (n m : ℕ) : ℝ :=
  Ch04.gammaTriangleConst 2 * (responseScoreRange d : ℝ) *
    (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) * A))

def accumulatedErrorWindowFluctuationScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (A : ℝ) (n m : ℕ) : ℝ :=
  let T := Ch04.gammaTriangleConst 2
  let Rlow := 2 * (8 / holderStoppingS) *
    (Ch04.gammaTriangleConst 2 * ((8 / holderStoppingS) * A))
  let Ractive := 2 * (8 / holderStoppingS) *
    accumulatedResponseActiveWindowScale d A n m
  let Flow := 2 * (Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * fieldOneGammaDimScale M *
      (6 / (holderStoppingS / 8) ^ 2) ^ 2))
  let Factive := 2 * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedFiniteFieldScaleBound M holderStoppingS))
  let Gactive := (3 / 2 : ℝ) *
    (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) *
          accumulatedGradientOwnRowScale M))
  let Gtail := (3 / 2 : ℝ) * accumulatedGradientEnvelopeScale M
  T * (T * (T * (T * (T * (Rlow + Ractive) + Flow) + Factive) + Gactive) + Gtail)

noncomputable def holderErrorResponseCoeff (d : ℕ) (C : ℝ) : ℝ :=
  Real.exp 1 * Real.sqrt (holderResponseGammaSqConst d C)

noncomputable def holderErrorFieldGammaCoeff (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) * Real.sqrt (shellCoverLogConst * (d : ℝ)) *
    (1 + Real.log 2) ^ (2 : ℝ)⁻¹

noncomputable def holderErrorFieldCubeCoeff (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) *
    (3 * Real.log ((shellCoverShifts d (0 : ℤ)).card : ℝ)) ^ (2 : ℝ)⁻¹ *
      (1 + Real.log 2) ^ (2 : ℝ)⁻¹

noncomputable def holderErrorFieldBoundCoeff (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 *
    (holderErrorFieldCubeCoeff d +
      16 * holderErrorFieldGammaCoeff d *
        (Real.sqrt (holderStoppingS / 8))⁻¹ * (holderStoppingS / 8)⁻¹)

noncomputable def holderErrorGradientOwnCoeff (d : ℕ) : ℝ :=
  (d : ℝ) * (1 + Real.log 2) ^ (2 : ℝ)⁻¹

noncomputable def holderErrorGradientEnvelopeCoeff (d : ℕ) : ℝ :=
  (d : ℝ) * IndependentSums.gammaTriangleConst 2 * (3 / 2 : ℝ) *
    (1 + Real.log 2) ^ (2 : ℝ)⁻¹

theorem holderResponseScale_eq_coeff_mul {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C : ℝ) :
    Real.exp 1 * holderResponseGammaScale M C =
      holderErrorResponseCoeff d C * M.delta * Real.sqrt |Real.log M.delta| := by
  unfold holderResponseGammaScale holderErrorResponseCoeff
  ring

theorem fieldOneGammaScale_eq_coeff_mul {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    fieldOneGammaDimScale M = holderErrorFieldGammaCoeff d * M.delta := by
  unfold fieldOneGammaDimScale holderErrorFieldGammaCoeff
  ring

theorem finiteFieldScaleBound_eq_coeff_mul {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    accumulatedFiniteFieldScaleBound M holderStoppingS =
      holderErrorFieldBoundCoeff d * M.delta := by
  unfold accumulatedFiniteFieldScaleBound holderErrorFieldBoundCoeff
    fieldOneCubeMajorantScale holderErrorFieldCubeCoeff
  rw [fieldOneGammaScale_eq_coeff_mul]
  norm_num
  ring

theorem gradientOwnScale_eq_coeff_mul {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    accumulatedGradientOwnRowScale M =
      holderErrorGradientOwnCoeff d * M.delta := by
  unfold accumulatedGradientOwnRowScale holderErrorGradientOwnCoeff
  ring

theorem gradientEnvelopeScale_eq_coeff_mul {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    accumulatedGradientEnvelopeScale M =
      holderErrorGradientEnvelopeCoeff d * M.delta := by
  unfold accumulatedGradientEnvelopeScale holderErrorGradientEnvelopeCoeff
  ring

noncomputable def holderErrorMeanCoeff (d : ℕ) (C : ℝ) : ℝ :=
  2 * (8 / holderStoppingS) *
      (IndependentSums.gammaMomentConst 2 * holderErrorResponseCoeff d C) +
    2 * (IndependentSums.gammaMomentConst 2 * holderErrorFieldBoundCoeff d) +
    (3 / 2 : ℝ) *
      (IndependentSums.gammaMomentConst 2 * holderErrorGradientOwnCoeff d)

noncomputable def holderErrorFluctuationCoeff (d : ℕ) (C : ℝ) : ℝ :=
  let T := Ch04.gammaTriangleConst 2
  let Rlow := 2 * (8 / holderStoppingS) *
    (Ch04.gammaTriangleConst 2 *
      ((8 / holderStoppingS) * holderErrorResponseCoeff d C))
  let Ractive := 2 * (8 / holderStoppingS) *
    (Ch04.gammaTriangleConst 2 * (responseScoreRange d : ℝ) *
      (Ch04.gammaSigmaIndependentSumConst 2 *
        ((1 + IndependentSums.gammaMomentConst 2) *
          holderErrorResponseCoeff d C)))
  let Flow := 2 * (Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * holderErrorFieldGammaCoeff d *
      (6 / (holderStoppingS / 8) ^ 2) ^ 2))
  let Factive := 2 * (Ch04.gammaSigmaIndependentSumConst 2 *
    ((1 + IndependentSums.gammaMomentConst 2) *
      holderErrorFieldBoundCoeff d))
  let Gactive := (3 / 2 : ℝ) *
    (Ch04.gammaSigmaIndependentSumConst 2 *
      ((1 + IndependentSums.gammaMomentConst 2) *
        holderErrorGradientOwnCoeff d))
  let Gtail := (3 / 2 : ℝ) * holderErrorGradientEnvelopeCoeff d
  T * (T * (T * (T * (T * (Rlow + Ractive) + Flow) + Factive) + Gactive) + Gtail)

theorem accumulatedErrorWindowMeanBound_le_coeff {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C : ℝ} (_hC : 0 < C)
    (n m : ℕ) :
    accumulatedErrorWindowMeanBound M
        (Real.exp 1 * holderResponseGammaScale M C) n m ≤
      ((m + 1 - n : ℕ) : ℝ) *
        (holderErrorMeanCoeff d C * M.delta *
          (1 + Real.sqrt |Real.log M.delta|)) := by
  have hroot : 0 ≤ Real.sqrt |Real.log M.delta| := Real.sqrt_nonneg _
  have hdelta := M.shellPrefix.delta_pos
  have hA := holderResponseScale_eq_coeff_mul M C
  have hF := finiteFieldScaleBound_eq_coeff_mul M
  have hG := gradientOwnScale_eq_coeff_mul M
  unfold accumulatedErrorWindowMeanBound holderErrorMeanCoeff
  rw [hA, hF, hG]
  have hcR : 0 ≤ 8 / holderStoppingS := by positivity [holderStoppingS_pos]
  have hgm : 0 ≤ IndependentSums.gammaMomentConst 2 :=
    (IndependentSums.gammaMomentConst_pos (by norm_num)).le
  have haC : 0 ≤ holderErrorResponseCoeff d C := by
    unfold holderErrorResponseCoeff
    exact mul_nonneg (Real.exp_pos _).le
      (Real.sqrt_nonneg _)
  have hfC : 0 ≤ holderErrorFieldBoundCoeff d := by
    have hpos := accumulatedFiniteFieldScaleBound_pos M holderStoppingS_pos
    rw [hF] at hpos
    have hpos' : 0 * M.delta < holderErrorFieldBoundCoeff d * M.delta := by
      simpa using! hpos
    exact ((mul_pos_iff_of_pos_right hdelta).mp (by simpa using! hpos')).le
  have hgC : 0 ≤ holderErrorGradientOwnCoeff d := by
    unfold holderErrorGradientOwnCoeff
    positivity
  let xR := 2 * (8 / holderStoppingS) *
    (IndependentSums.gammaMomentConst 2 * holderErrorResponseCoeff d C) * M.delta
  let xF := 2 *
    (IndependentSums.gammaMomentConst 2 * holderErrorFieldBoundCoeff d) * M.delta
  let xG := (3 / 2 : ℝ) *
    (IndependentSums.gammaMomentConst 2 * holderErrorGradientOwnCoeff d) * M.delta
  have hxR : 0 ≤ xR := by
    dsimp only [xR]
    positivity
  have hxF : 0 ≤ xF := by
    dsimp only [xF]
    positivity
  have hxG : 0 ≤ xG := by
    dsimp only [xG]
    positivity
  have hinside : xR * Real.sqrt |Real.log M.delta| + xF + xG ≤
      (xR + xF + xG) * (1 + Real.sqrt |Real.log M.delta|) := by
    nlinarith [mul_nonneg (add_nonneg hxF hxG) hroot]
  have hwindow : 0 ≤ ((m + 1 - n : ℕ) : ℝ) := Nat.cast_nonneg _
  apply mul_le_mul_of_nonneg_left _ hwindow
  convert hinside using 1 <;> dsimp only [xR, xF, xG] <;> ring

theorem accumulatedErrorWindowFluctuationScale_le_coeff
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C : ℝ} (_hC : 0 < C)
    {n m : ℕ} (hnm : n ≤ m) :
    accumulatedErrorWindowFluctuationScale M
        (Real.exp 1 * holderResponseGammaScale M C) n m ≤
      holderErrorFluctuationCoeff d C * M.delta *
        (1 + Real.sqrt |Real.log M.delta|) *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
  let root := Real.sqrt |Real.log M.delta|
  let Wroot := Real.sqrt ((m + 1 - n : ℕ) : ℝ)
  have hroot : 0 ≤ root := Real.sqrt_nonneg _
  have hwindow : 0 < m + 1 - n := by omega
  have hW : 1 ≤ Wroot := by
    have hcast : (1 : ℝ) ≤ ((m + 1 - n : ℕ) : ℝ) := by exact_mod_cast hwindow
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hcast
  have hdelta := M.shellPrefix.delta_pos
  have hA := holderResponseScale_eq_coeff_mul M C
  have hD := fieldOneGammaScale_eq_coeff_mul M
  have hF := finiteFieldScaleBound_eq_coeff_mul M
  have hG := gradientOwnScale_eq_coeff_mul M
  have hGE := gradientEnvelopeScale_eq_coeff_mul M
  unfold accumulatedErrorWindowFluctuationScale
    holderErrorFluctuationCoeff accumulatedResponseActiveWindowScale
  rw [hA, hD, hF, hG, hGE]
  dsimp only [root, Wroot]
  have htri : 0 ≤ Ch04.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos.le
  have hind : 0 ≤ Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos.le
  have hgm : 0 ≤ IndependentSums.gammaMomentConst 2 :=
    (IndependentSums.gammaMomentConst_pos (by norm_num)).le
  have hcR : 0 ≤ 8 / holderStoppingS := by positivity [holderStoppingS_pos]
  have hrespC : 0 ≤ holderErrorResponseCoeff d C := by
    unfold holderErrorResponseCoeff
    positivity
  have hfieldGammaC : 0 ≤ holderErrorFieldGammaCoeff d := by
    unfold holderErrorFieldGammaCoeff
    positivity
  have hfieldBoundC : 0 ≤ holderErrorFieldBoundCoeff d := by
    have hpos := accumulatedFiniteFieldScaleBound_pos M holderStoppingS_pos
    rw [hF] at hpos
    have hpos' : 0 * M.delta < holderErrorFieldBoundCoeff d * M.delta := by
      simpa using! hpos
    exact ((mul_pos_iff_of_pos_right hdelta).mp (by simpa using! hpos')).le
  have hgradientOwnC : 0 ≤ holderErrorGradientOwnCoeff d := by
    unfold holderErrorGradientOwnCoeff
    positivity
  have hgradientEnvelopeC : 0 ≤ holderErrorGradientEnvelopeCoeff d := by
    unfold holderErrorGradientEnvelopeCoeff
    positivity
  have hcommon : 0 ≤ M.delta * (1 + Real.sqrt |Real.log M.delta|) *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by positivity
  let common := M.delta * (1 + Real.sqrt |Real.log M.delta|) *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ)
  have hdeltaRoot : M.delta * Real.sqrt |Real.log M.delta| ≤ common := by
    calc
      M.delta * Real.sqrt |Real.log M.delta| ≤
          M.delta * (1 + Real.sqrt |Real.log M.delta|) := by
        gcongr
        linarith
      _ ≤ common := le_mul_of_one_le_right (by positivity) hW
  have hdeltaRootWindow : M.delta * Real.sqrt |Real.log M.delta| *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) ≤ common := by
    unfold common
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith :
        Real.sqrt |Real.log M.delta| ≤ 1 + Real.sqrt |Real.log M.delta|)
        hdelta.le) (Real.sqrt_nonneg _)
  have hdeltaWindow : M.delta * Real.sqrt ((m + 1 - n : ℕ) : ℝ) ≤ common := by
    have h : (M.delta * 1) * Real.sqrt ((m + 1 - n : ℕ) : ℝ) ≤
        (M.delta * (1 + Real.sqrt |Real.log M.delta|)) *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : 1 ≤
        1 + Real.sqrt |Real.log M.delta|) hdelta.le)
      (Real.sqrt_nonneg _)
    unfold common
    convert h using 1
    all_goals ring
  have hdeltaOnly : M.delta ≤ common := by
    calc
      M.delta ≤ M.delta * (1 + Real.sqrt |Real.log M.delta|) :=
        le_mul_of_one_le_right hdelta.le (by linarith)
      _ ≤ common := le_mul_of_one_le_right (by positivity) hW
  let T := Ch04.gammaTriangleConst 2
  let RlowC := 2 * (8 / holderStoppingS) *
    (Ch04.gammaTriangleConst 2 *
      ((8 / holderStoppingS) * holderErrorResponseCoeff d C))
  let RactiveC := 2 * (8 / holderStoppingS) *
    (Ch04.gammaTriangleConst 2 * (responseScoreRange d : ℝ) *
      (Ch04.gammaSigmaIndependentSumConst 2 *
        ((1 + IndependentSums.gammaMomentConst 2) *
          holderErrorResponseCoeff d C)))
  let FlowC := 2 * (Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * holderErrorFieldGammaCoeff d *
      (6 / (holderStoppingS / 8) ^ 2) ^ 2))
  let FactiveC := 2 * (Ch04.gammaSigmaIndependentSumConst 2 *
    ((1 + IndependentSums.gammaMomentConst 2) *
      holderErrorFieldBoundCoeff d))
  let GactiveC := (3 / 2 : ℝ) *
    (Ch04.gammaSigmaIndependentSumConst 2 *
      ((1 + IndependentSums.gammaMomentConst 2) *
        holderErrorGradientOwnCoeff d))
  let GtailC := (3 / 2 : ℝ) * holderErrorGradientEnvelopeCoeff d
  have hRlowC : 0 ≤ RlowC := by
    dsimp only [RlowC]
    positivity
  have hRactiveC : 0 ≤ RactiveC := by
    dsimp only [RactiveC]
    positivity
  have hFlowC : 0 ≤ FlowC := by
    dsimp only [FlowC]
    positivity
  have hFactiveC : 0 ≤ FactiveC := by
    dsimp only [FactiveC]
    positivity
  have hGactiveC : 0 ≤ GactiveC := by
    dsimp only [GactiveC]
    positivity
  have hGtailC : 0 ≤ GtailC := by
    dsimp only [GtailC]
    positivity
  have hRlow :
      2 * (8 / holderStoppingS) *
          (Ch04.gammaTriangleConst 2 *
            (8 / holderStoppingS *
              (holderErrorResponseCoeff d C * M.delta *
                Real.sqrt |Real.log M.delta|))) ≤ RlowC * common := by
    calc
      _ = RlowC * (M.delta * Real.sqrt |Real.log M.delta|) := by
        dsimp only [RlowC]
        ring
      _ ≤ RlowC * common := mul_le_mul_of_nonneg_left hdeltaRoot hRlowC
  have hRactive :
      2 * (8 / holderStoppingS) *
          (Ch04.gammaTriangleConst 2 * (responseScoreRange d : ℝ) *
            (Ch04.gammaSigmaIndependentSumConst 2 *
              Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
                ((1 + IndependentSums.gammaMomentConst 2) *
                  (holderErrorResponseCoeff d C * M.delta *
                    Real.sqrt |Real.log M.delta|)))) ≤ RactiveC * common := by
    calc
      _ = RactiveC * (M.delta * Real.sqrt |Real.log M.delta| *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := by
        dsimp only [RactiveC]
        ring
      _ ≤ RactiveC * common :=
        mul_le_mul_of_nonneg_left hdeltaRootWindow hRactiveC
  have hFlow :
      2 * (Ch04.gammaTriangleConst 2 *
        (Ch04.gammaTriangleConst 2 *
          (holderErrorFieldGammaCoeff d * M.delta) *
            (6 / (holderStoppingS / 8) ^ 2) ^ 2)) ≤ FlowC * common := by
    calc
      _ = FlowC * M.delta := by
        dsimp only [FlowC]
        ring
      _ ≤ FlowC * common := mul_le_mul_of_nonneg_left hdeltaOnly hFlowC
  have hFactive :
      2 * (Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
          ((1 + IndependentSums.gammaMomentConst 2) *
            (holderErrorFieldBoundCoeff d * M.delta))) ≤ FactiveC * common := by
    calc
      _ = FactiveC *
          (M.delta * Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := by
        dsimp only [FactiveC]
        ring
      _ ≤ FactiveC * common :=
        mul_le_mul_of_nonneg_left hdeltaWindow hFactiveC
  have hGactive :
      (3 / 2 : ℝ) *
        (Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
            ((1 + IndependentSums.gammaMomentConst 2) *
              (holderErrorGradientOwnCoeff d * M.delta))) ≤ GactiveC * common := by
    calc
      _ = GactiveC *
          (M.delta * Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := by
        dsimp only [GactiveC]
        ring
      _ ≤ GactiveC * common :=
        mul_le_mul_of_nonneg_left hdeltaWindow hGactiveC
  have hGtail : (3 / 2 : ℝ) *
      (holderErrorGradientEnvelopeCoeff d * M.delta) ≤ GtailC * common := by
    calc
      _ = GtailC * M.delta := by
        dsimp only [GtailC]
        ring
      _ ≤ GtailC * common := mul_le_mul_of_nonneg_left hdeltaOnly hGtailC
  calc
    _ ≤
      T * (T * (T * (T * (T *
        (RlowC * common + RactiveC * common) + FlowC * common) +
          FactiveC * common) + GactiveC * common) + GtailC * common) := by
      gcongr
    _ = holderErrorFluctuationCoeff d C * common := by
      dsimp only [T, RlowC, RactiveC, FlowC, FactiveC, GactiveC, GtailC,
        holderErrorFluctuationCoeff]
      ring
    _ = _ := by
      unfold common holderErrorFluctuationCoeff
      ring

noncomputable def holderLogAbsorption : ℝ :=
  1 + (Real.sqrt (Real.log 2))⁻¹

noncomputable def holderErrorWindowCoeff (d : ℕ) (C : ℝ) : ℝ :=
  (1 + |holderErrorMeanCoeff d C| + |holderErrorFluctuationCoeff d C|) *
    holderLogAbsorption

theorem holderLogAbsorption_pos : 0 < holderLogAbsorption := by
  unfold holderLogAbsorption
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem one_add_sqrt_abs_log_le_holderLogAbsorption_mul {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    1 + Real.sqrt |Real.log M.delta| ≤
      holderLogAbsorption * Real.sqrt |Real.log M.delta| := by
  let a := Real.sqrt (Real.log 2)
  let r := Real.sqrt |Real.log M.delta|
  have ha : 0 < a := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  have har : a ≤ r := by
    dsimp only [a, r]
    exact Real.sqrt_le_sqrt (log_two_le_abs_log_delta M)
  have hone : 1 ≤ a⁻¹ * r := by
    calc
      1 = a⁻¹ * a := by field_simp [ha.ne']
      _ ≤ a⁻¹ * r := mul_le_mul_of_nonneg_left har (inv_nonneg.mpr ha.le)
  dsimp only [a, r] at hone
  unfold holderLogAbsorption
  nlinarith [Real.sqrt_nonneg |Real.log M.delta|]

theorem holderErrorWindowCoeff_pos (d : ℕ) (C : ℝ) :
    0 < holderErrorWindowCoeff d C := by
  unfold holderErrorWindowCoeff
  have hbase : 0 < 1 + |holderErrorMeanCoeff d C| +
      |holderErrorFluctuationCoeff d C| := by positivity
  exact mul_pos hbase holderLogAbsorption_pos

/-- Dimension-only coefficient form of the complete fixed-centre window
estimate.  Both the retained mean and Gamma-two scale use the same constant. -/
theorem accumulatedErrorWindow_bounds {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C : ℝ} (hC : 0 < C)
    {n m : ℕ} (hnm : n ≤ m) :
    accumulatedErrorWindowMeanBound M
        (Real.exp 1 * holderResponseGammaScale M C) n m ≤
      ((m + 1 - n : ℕ) : ℝ) *
        (holderErrorWindowCoeff d C * M.delta *
          Real.sqrt |Real.log M.delta|) ∧
    accumulatedErrorWindowFluctuationScale M
        (Real.exp 1 * holderResponseGammaScale M C) n m ≤
      holderErrorWindowCoeff d C * M.delta *
        Real.sqrt |Real.log M.delta| *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
  have hmean := accumulatedErrorWindowMeanBound_le_coeff M hC n m
  have hfluct := accumulatedErrorWindowFluctuationScale_le_coeff M hC hnm
  have hlog := one_add_sqrt_abs_log_le_holderLogAbsorption_mul M
  have hdelta := M.shellPrefix.delta_pos.le
  have hroot := Real.sqrt_nonneg |Real.log M.delta|
  have hmeanCoeff : holderErrorMeanCoeff d C ≤
      1 + |holderErrorMeanCoeff d C| + |holderErrorFluctuationCoeff d C| := by
    exact (le_abs_self _).trans (by linarith [abs_nonneg (holderErrorFluctuationCoeff d C)])
  have hfluctCoeff : holderErrorFluctuationCoeff d C ≤
      1 + |holderErrorMeanCoeff d C| + |holderErrorFluctuationCoeff d C| := by
    exact (le_abs_self _).trans (by linarith [abs_nonneg (holderErrorMeanCoeff d C)])
  have hmeanScale : holderErrorMeanCoeff d C * M.delta *
        (1 + Real.sqrt |Real.log M.delta|) ≤
      holderErrorWindowCoeff d C * M.delta *
        Real.sqrt |Real.log M.delta| := by
    unfold holderErrorWindowCoeff
    calc
      holderErrorMeanCoeff d C * M.delta *
          (1 + Real.sqrt |Real.log M.delta|) ≤
        (1 + |holderErrorMeanCoeff d C| + |holderErrorFluctuationCoeff d C|) *
          M.delta * (1 + Real.sqrt |Real.log M.delta|) := by gcongr
      _ ≤ (1 + |holderErrorMeanCoeff d C| + |holderErrorFluctuationCoeff d C|) *
          M.delta * (holderLogAbsorption * Real.sqrt |Real.log M.delta|) := by
        gcongr
      _ = (1 + |holderErrorMeanCoeff d C| + |holderErrorFluctuationCoeff d C|) *
          holderLogAbsorption * M.delta * Real.sqrt |Real.log M.delta| := by ring
  have hfluctScale : holderErrorFluctuationCoeff d C * M.delta *
        (1 + Real.sqrt |Real.log M.delta|) ≤
      holderErrorWindowCoeff d C * M.delta *
        Real.sqrt |Real.log M.delta| := by
    unfold holderErrorWindowCoeff
    calc
      holderErrorFluctuationCoeff d C * M.delta *
          (1 + Real.sqrt |Real.log M.delta|) ≤
        (1 + |holderErrorMeanCoeff d C| + |holderErrorFluctuationCoeff d C|) *
          M.delta * (1 + Real.sqrt |Real.log M.delta|) := by gcongr
      _ ≤ (1 + |holderErrorMeanCoeff d C| + |holderErrorFluctuationCoeff d C|) *
          M.delta * (holderLogAbsorption * Real.sqrt |Real.log M.delta|) := by
        gcongr
      _ = (1 + |holderErrorMeanCoeff d C| + |holderErrorFluctuationCoeff d C|) *
          holderLogAbsorption * M.delta * Real.sqrt |Real.log M.delta| := by ring
  constructor
  · exact hmean.trans (mul_le_mul_of_nonneg_left hmeanScale (Nat.cast_nonneg _))
  · exact hfluct.trans
      (mul_le_mul_of_nonneg_right hfluctScale (Real.sqrt_nonneg _))

/-- Complete one-centre reduction to a deterministic linear mean and one
Gamma-two fluctuation carrier. -/
theorem ae_sum_accumulatedError_le_mean_add_fluctuation
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (holderResponseRow M j) A) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M none k z holderStoppingS omega) ≤
        accumulatedErrorWindowMeanBound M A n m +
          accumulatedErrorWindowFluctuation M z n m omega := by
  filter_upwards [ae_sum_accumulatedError_le_carriers M z hnm] with omega hcarrier
  have hrespLow := accumulatedResponseLowWindow_le_decay_rows
    M n m (translatePotentialSample z omega)
  have hrespLow' : accumulatedResponseLowWindow M n m
      (translatePotentialSample z omega) ≤
      (8 / holderStoppingS) * accumulatedResponseLowRows M n
        (translatePotentialSample z omega) := by
    simpa only [accumulatedResponseLowRows] using! hrespLow
  have hrespActive := accumulatedResponseActiveWindow_le_centered_add_mean
    M n m hA hrow (translatePotentialSample z omega)
  have hfieldActive := accumulatedFiniteFieldActiveWindow_le_centered_add_mean
    M z holderStoppingS_pos (by norm_num [holderStoppingS]) hnm omega
  have hgradMean := sum_accumulatedGradientOwnRow_le_centered_add_mean
    M z n m omega
  unfold accumulatedErrorWindowMeanBound accumulatedErrorWindowFluctuation
  have hconst : 0 ≤ 8 / holderStoppingS := by positivity [holderStoppingS_pos]
  calc
    _ ≤ 2 * (accumulatedResponseLowWindow M n m
              (translatePotentialSample z omega) +
            accumulatedResponseActiveWindow M n m
              (translatePotentialSample z omega)) +
        2 * (accumulatedFiniteFieldLowWindow z holderStoppingS n m omega +
            accumulatedFiniteFieldActiveWindow z holderStoppingS n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := hcarrier
    _ ≤ 2 * ((8 / holderStoppingS) * accumulatedResponseLowRows M n
              (translatePotentialSample z omega) +
            (8 / holderStoppingS) *
              (centeredHolderResponseWindow M n m
                  (translatePotentialSample z omega) +
                ((m + 1 - n : ℕ) : ℝ) * (IndependentSums.gammaMomentConst 2 * A))) +
        2 * (accumulatedFiniteFieldLowWindow z holderStoppingS n m omega +
          (centeredAccumulatedFiniteFieldActiveWindow M z holderStoppingS n m omega +
            ((m + 1 - n : ℕ) : ℝ) *
              (IndependentSums.gammaMomentConst 2 *
                accumulatedFiniteFieldScaleBound M holderStoppingS))) +
        (3 / 2 : ℝ) *
          ((centeredAccumulatedGradientWindow M z n m omega +
              ((m + 1 - n : ℕ) : ℝ) *
                (IndependentSums.gammaMomentConst 2 * accumulatedGradientOwnRowScale M)) +
            accumulatedGradientEnvelope m z omega) := by
      gcongr
    _ = ((m + 1 - n : ℕ) : ℝ) *
          (2 * (8 / holderStoppingS) * (IndependentSums.gammaMomentConst 2 * A) +
            2 * (IndependentSums.gammaMomentConst 2 *
              accumulatedFiniteFieldScaleBound M holderStoppingS) +
            (3 / 2 : ℝ) *
              (IndependentSums.gammaMomentConst 2 * accumulatedGradientOwnRowScale M)) +
        (2 * (8 / holderStoppingS) *
          (accumulatedResponseLowRows M n (translatePotentialSample z omega) +
            centeredHolderResponseWindow M n m (translatePotentialSample z omega)) +
        2 * (accumulatedFiniteFieldLowWindow z holderStoppingS n m omega +
          centeredAccumulatedFiniteFieldActiveWindow M z holderStoppingS n m omega) +
        (3 / 2 : ℝ) *
          (centeredAccumulatedGradientWindow M z n m omega +
            accumulatedGradientEnvelope m z omega)) := by ring

/-- The one-centre fluctuation is Gamma-two at the exact scale assembled
from the six independent/triangle components. -/
theorem isBigO_accumulatedErrorWindowFluctuation
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (holderResponseRow M j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (accumulatedErrorWindowFluctuation M z n m)
      (accumulatedErrorWindowFluctuationScale M A n m) := by
  let cR : ℝ := 2 * (8 / holderStoppingS)
  let cF : ℝ := 2
  let cG : ℝ := 3 / 2
  let Rlow : ℝ := cR *
    (Ch04.gammaTriangleConst 2 * ((8 / holderStoppingS) * A))
  let Ractive : ℝ := cR * accumulatedResponseActiveWindowScale d A n m
  let Flow : ℝ := cF * (Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * fieldOneGammaDimScale M *
      (6 / (holderStoppingS / 8) ^ 2) ^ 2))
  let Factive : ℝ := cF * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedFiniteFieldScaleBound M holderStoppingS))
  let Gactive : ℝ := cG * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedGradientOwnRowScale M))
  let Gtail : ℝ := cG * accumulatedGradientEnvelopeScale M
  have hcR : 0 < cR := by unfold cR; positivity [holderStoppingS_pos]
  have hcF : 0 < cF := by unfold cF; norm_num
  have hcG : 0 < cG := by unfold cG; norm_num
  have hwindow : 0 < m + 1 - n := by omega
  have hsqrt : 0 < Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hwindow)
  have htri : 0 < Ch04.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hind : 0 < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hmoment : 0 < 1 + IndependentSums.gammaMomentConst 2 :=
    add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hRlow : 0 < Rlow := by
    unfold Rlow
    exact mul_pos hcR (mul_pos htri
      (mul_pos (by positivity [holderStoppingS_pos]) hA))
  have hRactive : 0 < Ractive := by
    unfold Ractive accumulatedResponseActiveWindowScale
    have hr : 0 < (responseScoreRange d : ℝ) := by
      exact_mod_cast responseScoreRange_pos d
    positivity
  have hFlow : 0 < Flow := by
    unfold Flow
    have hden : 0 < (holderStoppingS / 8) ^ 2 := by
      exact sq_pos_of_pos (by positivity [holderStoppingS_pos])
    have hsix : 0 < 6 / (holderStoppingS / 8) ^ 2 := div_pos (by norm_num) hden
    exact mul_pos hcF (mul_pos htri
      (mul_pos (mul_pos htri (fieldOneGammaDimScale_pos_stopping M))
        (sq_pos_of_pos hsix)))
  have hFactive : 0 < Factive := by
    unfold Factive
    positivity [accumulatedFiniteFieldScaleBound_pos M holderStoppingS_pos]
  have hGactive : 0 < Gactive := by
    unfold Gactive
    positivity [accumulatedGradientOwnRowScale_pos M]
  have hEnvelopeScale : 0 < accumulatedGradientEnvelopeScale M := by
    unfold accumulatedGradientEnvelopeScale
    have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
    have hlog : 0 < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    exact mul_pos (mul_pos (mul_pos hd
      IndependentSums.gammaTriangleConst_pos) (by norm_num))
      (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos)
  have hGtail : 0 < Gtail := by unfold Gtail; positivity
  let X1 : Sample d → ℝ := fun omega ↦ cR *
    accumulatedResponseLowRows M n (translatePotentialSample z omega)
  let X2 : Sample d → ℝ := fun omega ↦ cR *
    centeredHolderResponseWindow M n m (translatePotentialSample z omega)
  let X3 : Sample d → ℝ := fun omega ↦ cF *
    accumulatedFiniteFieldLowWindow z holderStoppingS n m omega
  let X4 : Sample d → ℝ := fun omega ↦ cF *
    centeredAccumulatedFiniteFieldActiveWindow M z holderStoppingS n m omega
  let X5 : Sample d → ℝ := fun omega ↦ cG *
    centeredAccumulatedGradientWindow M z n m omega
  let X6 : Sample d → ℝ := fun omega ↦ cG * accumulatedGradientEnvelope m z omega
  have hX1 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X1 Rlow := by
    have hbase := isBigO_comp_translatePotentialSample M z
      (isBigO_accumulatedResponseLowRows M n hA hrow)
    simpa only [X1, Rlow] using! hbase.const_mul hcR.le
  have hX2 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X2 Ractive := by
    have hbase0 := isBigO_centeredHolderResponseWindow M
      (responseScoreRange d) n m (responseScoreRange_pos d) hnm
      (columnsIndep_holderResponseRowArray M) hA hrow
    have hbase := isBigO_comp_translatePotentialSample M z hbase0
    simpa only [X2, Ractive, accumulatedResponseActiveWindowScale] using!
      hbase.const_mul hcR.le
  have hX3 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X3 Flow := by
    have hbase := isBigO_accumulatedFiniteFieldLowWindow M z
      holderStoppingS_pos (by norm_num [holderStoppingS]) hnm
    simpa only [X3, Flow] using! hbase.const_mul hcF.le
  have hX4 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X4 Factive := by
    have hbase := isBigO_centeredAccumulatedFiniteFieldActiveWindow_le_bound
      M z holderStoppingS_pos (by norm_num [holderStoppingS]) hnm
    simpa only [X4, Factive] using! hbase.const_mul hcF.le
  have hX5 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X5 Gactive := by
    have hbase := isBigO_centeredAccumulatedGradientWindow M z hnm
    simpa only [X5, Gactive] using! hbase.const_mul hcG.le
  have hX6 : IndependentSums.IsBigO M.P.toMeasure
      (IndependentSums.gammaSigma 2) X6 Gtail := by
    have hbase0 := isBigOWith_gammaTwo_accumulatedGradientEnvelope M m z
    have hbase : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (accumulatedGradientEnvelope m z)
        (accumulatedGradientEnvelopeScale M) := by
      simpa [IndependentSums.IsBigO,
        abs_of_nonneg (accumulatedGradientEnvelope_nonneg m z _)] using! hbase0
    simpa only [X6, Gtail] using! hbase.const_mul hcG.le
  have hm1 : AEMeasurable X1 M.P.toMeasure := by
    exact ((measurable_accumulatedResponseLowRows M n).comp
      (Section6Covariance.measurable_translatePotentialSample z)).const_mul _ |>.aemeasurable
  have hm2 : AEMeasurable X2 M.P.toMeasure := by
    exact ((measurable_centeredHolderResponseWindow M n m).comp
      (Section6Covariance.measurable_translatePotentialSample z)).const_mul _ |>.aemeasurable
  have hm3 : AEMeasurable X3 M.P.toMeasure :=
    (measurable_accumulatedFiniteFieldLowWindow z holderStoppingS n m).const_mul _ |>.aemeasurable
  have hm4 : AEMeasurable X4 M.P.toMeasure :=
    (measurable_centeredAccumulatedFiniteFieldActiveWindow M z holderStoppingS n m).const_mul _ |>.aemeasurable
  have hm5 : AEMeasurable X5 M.P.toMeasure :=
    (measurable_centeredAccumulatedGradientWindow M z n m).const_mul _ |>.aemeasurable
  have hm6 : AEMeasurable X6 M.P.toMeasure :=
    (aemeasurable_accumulatedGradientEnvelope M m z).const_mul _
  have h12 := isBigO_add_gammaTwo M hRlow hRactive hX1 hX2 hm1 hm2
  have hm12 := hm1.add hm2
  have h123 := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos hRlow hRactive)) hFlow h12 hX3 hm12 hm3
  have hm123 := hm12.add hm3
  have h1234 := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos (mul_pos htri (add_pos hRlow hRactive)) hFlow))
    hFactive h123 hX4 hm123 hm4
  have hm1234 := hm123.add hm4
  have h12345 := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos
      (mul_pos htri (add_pos (mul_pos htri (add_pos hRlow hRactive)) hFlow))
      hFactive)) hGactive h1234 hX5 hm1234 hm5
  have hm12345 := hm1234.add hm5
  have hall := isBigO_add_gammaTwo M
    (mul_pos htri (add_pos
      (mul_pos htri (add_pos
        (mul_pos htri (add_pos (mul_pos htri (add_pos hRlow hRactive)) hFlow))
        hFactive)) hGactive)) hGtail h12345 hX6 hm12345 hm6
  convert hall using 1
  · funext omega
    unfold accumulatedErrorWindowFluctuation X1 X2 X3 X4 X5 X6 cR cF cG
    ring
  · rfl

/-- Exact one-centre sub-Gaussian tail before the dimension-only numerical
absorption. -/
theorem measureReal_accumulatedError_oneCenter_le_exp {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A threshold t : ℝ}
    (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (holderResponseRow M j) A)
    (ht : 1 ≤ t)
    (hthreshold : accumulatedErrorWindowMeanBound M A n m +
      accumulatedErrorWindowFluctuationScale M A n m * t ≤ threshold) :
    M.P.toMeasure.real {omega | threshold <
        ∑ k ∈ Finset.Icc n m,
          accumulatedError M none k z holderStoppingS omega} ≤
      Real.exp (-(t ^ (2 : ℝ))) := by
  have hbig := isBigO_accumulatedErrorWindowFluctuation M z hnm hA hrow
  have htail := (IndependentSums.isBigO_gammaSigma_iff.mp hbig) ht
  have hae : {omega | threshold <
      ∑ k ∈ Finset.Icc n m,
        accumulatedError M none k z holderStoppingS omega} ≤ᵐ[M.P.toMeasure]
      IndependentSums.absTailEvent
        (accumulatedErrorWindowFluctuation M z n m)
        (accumulatedErrorWindowFluctuationScale M A n m * t) := by
    filter_upwards [ae_sum_accumulatedError_le_mean_add_fluctuation
      M z hnm hA hrow] with omega hupper
    intro homega
    change threshold < ∑ k ∈ Finset.Icc n m,
      accumulatedError M none k z holderStoppingS omega at homega
    unfold IndependentSums.absTailEvent IndependentSums.upperTailEvent
    dsimp only [Set.mem_ofPred_eq]
    have hfluct : accumulatedErrorWindowFluctuationScale M A n m * t <
        accumulatedErrorWindowFluctuation M z n m omega := by linarith
    exact hfluct.trans_le (le_abs_self _)
  have hmeasure := MeasureTheory.measure_mono_ae hae
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
  exact hreal.trans htail

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
