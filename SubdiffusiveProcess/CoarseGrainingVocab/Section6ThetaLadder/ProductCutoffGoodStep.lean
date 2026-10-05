module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.CutoffPaperError
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductErrorLocalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductTranslatedRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.GoodScaleClause

@[expose] public section

/-!
# Theta-perturbed ladder: the finite-cutoff good-scale recurrence

This module inserts the proved finite-cutoff good-scale error bound into the
translated product recurrence.  The parent paper error is read from the good
event, the two-scale inner error is obtained by deterministic descendant
localization, and the multiplier sensitivity is paid once as `sqrt epsilon`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- Universal price for restricting the parent paper error two scales. -/
def productTwoScaleErrorFactor : ℝ :=
  1 + Real.sqrt (Real.rpow 3 ((1 / 32 : ℝ) * 4))

theorem productTwoScaleErrorFactor_pos : 0 < productTwoScaleErrorFactor := by
  unfold productTwoScaleErrorFactor
  positivity

theorem productTwoScaleErrorFactor_ge_one :
    1 ≤ productTwoScaleErrorFactor := by
  unfold productTwoScaleErrorFactor
  linarith [Real.sqrt_nonneg (Real.rpow 3 ((1 / 32 : ℝ) * 4))]

/-- The cutoff good event gives one common real cap for the parent paper
error and its two-scale descendant. -/
theorem cutoffGoodEvent_parent_inner_paperError_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {eta C : ℝ} (hC : 0 ≤ C)
    (hs : 64 * M.delta ^ 2 ≤ (1 / 32 : ℝ))
    (heta : eta ∈ Set.Icc ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1)
    (hgood : omega ∈ goodEvent M (some L) n z eta (1 / 32 : ℝ))
    (herror : section6HomogenizationError M (1 / 32 : ℝ) L n omega z ≤ C * eta) :
    let alpha := tailCoefficientCubeAverage M L n
      (translatePotentialSample z omega)
    paperHomogenizationError (originCube d (n : ℤ)) (n : ℤ) (1 / 32 : ℝ)
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega)) alpha ≤
          ENNReal.ofReal (productTwoScaleErrorFactor * C * eta) ∧
      paperHomogenizationError (originCube d ((n : ℤ) - 2)) ((n : ℤ) - 2)
        (1 / 32 : ℝ) .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega)) alpha ≤
          ENNReal.ofReal (productTwoScaleErrorFactor * C * eta) := by
  dsimp only
  have heta0 : 0 ≤ eta := by
    have hlow : 0 ≤ (1 / 32 : ℝ)⁻¹ * M.delta ^ 2 := by positivity
    exact hlow.trans heta.1
  have hparentEq := paperHomogenizationError_eq_ofReal_cutoffGoodEvent
    M (s := (1 / 32 : ℝ)) hs (by norm_num)
      L n omega z heta0 heta.2 hgood
  have hparentC : paperHomogenizationError (originCube d (n : ℤ)) (n : ℤ)
      (1 / 32 : ℝ) .infinity (.finite 2)
      (aCutoffFamily M L (translatePotentialSample z omega))
      (tailCoefficientCubeAverage M L n (translatePotentialSample z omega)) ≤
        ENNReal.ofReal (C * eta) := by
    rw [hparentEq]
    exact ENNReal.ofReal_le_ofReal herror
  have hparent : paperHomogenizationError (originCube d (n : ℤ)) (n : ℤ)
      (1 / 32 : ℝ) .infinity (.finite 2)
      (aCutoffFamily M L (translatePotentialSample z omega))
      (tailCoefficientCubeAverage M L n (translatePotentialSample z omega)) ≤
        ENNReal.ofReal (productTwoScaleErrorFactor * C * eta) := by
    refine hparentC.trans (ENNReal.ofReal_le_ofReal ?_)
    have hCE : 0 ≤ C * eta := mul_nonneg hC heta0
    calc
      C * eta ≤ productTwoScaleErrorFactor * (C * eta) :=
        (by simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right productTwoScaleErrorFactor_ge_one hCE))
      _ = productTwoScaleErrorFactor * C * eta := by ring
  have hinnerRaw := paperHomogenizationError_two_origin_pred_two_le
    (d := d) (n : ℤ) (aCutoffFamily M L (translatePotentialSample z omega))
      (tailCoefficientCubeAverage M L n (translatePotentialSample z omega))
      (1 / 32 : ℝ)
  have hR0 : 0 ≤ Real.rpow 3 ((1 / 32 : ℝ) * 4) :=
    Real.rpow_nonneg (by norm_num) _
  have hfactor :
      (ENNReal.ofReal (Real.rpow 3 ((1 / 32 : ℝ) * 4))) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt (Real.rpow 3 ((1 / 32 : ℝ) * 4))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hR0 (by norm_num)]
    rw [Real.sqrt_eq_rpow]
  have hinnerC := hinnerRaw.trans (by
    exact mul_le_mul' le_rfl hparentC)
  refine ⟨hparent, hinnerC.trans ?_⟩
  rw [hfactor, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hCE : 0 ≤ C * eta := mul_nonneg hC heta0
  unfold productTwoScaleErrorFactor
  nlinarith [Real.sqrt_nonneg (Real.rpow 3 ((1 / 32 : ℝ) * 4))]

/-- The physical product recurrence on a finite-cutoff good scale.  Its only
new term is the displayed `sqrt epsilon` sensitivity price. -/
theorem exists_productTranslated_goodScaleRecurrence (d : ℕ) [NeZero d] :
    ∃ Kbase Cgain : ℝ, 0 < Kbase ∧ 0 < Cgain ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
      ∀ L n : ℕ, ∀ z : Vec d, ∀ omega,
      ∀ eta ∈ Set.Icc ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1,
      omega ∈ goodEvent M (some L) n z eta (1 / 32 : ℝ) →
      ∀ b epsilon : ℝ, 0 < b → 0 < epsilon → epsilon ≤ 1 / 2 →
      Kbase * eta + Cgain * Real.sqrt epsilon ≤ 1 →
      ∀ theta : Vec d → ℝ,
      ContinuousOn theta (translatedCube d (n : ℤ) z) →
      (∀ x ∈ translatedCube d (n : ℤ) z,
        |b⁻¹ * theta x - 1| ≤ epsilon) →
      ∀ k : ℕ, 6 ≤ k →
      ∀ u : H1Function (translatedCube d (n : ℤ) z),
      IsWeaklyHarmonicOn
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x)
        (translatedCube d (n : ℤ) z) u →
      ∀ ell : Affine d,
      ell ∈ affineMinimizers (translatedCube d (n : ℤ) z) u.toFun →
      excess ((n : ℤ) - (k : ℤ))
          (translatedCube d ((n : ℤ) - (k : ℤ)) z) u.toFun ≤
        oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
            ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
            excess (n : ℤ) (translatedCube d (n : ℤ) z) u.toFun +
          productOriginRecurrenceErrorConstant d M.shellPrefix.dimension k *
            (Kbase * eta + Cgain * Real.sqrt epsilon) *
            (excess (n : ℤ) (translatedCube d (n : ℤ) z) u.toFun +
              Real.sqrt (d : ℝ) / 2 * Real.sqrt (vecNormSq ell.slope)) := by
  obtain ⟨C, hC, hgoodCap⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.exists_cutoff_regularity_good_scale_clause d
  let Kbase := productTwoScaleErrorFactor * C
  let Cgain := 8 * Kbase + Real.sqrt 15
  have hKbase : 0 < Kbase := mul_pos productTwoScaleErrorFactor_pos hC
  have hCgain : 0 < Cgain := by dsimp only [Cgain]; positivity
  refine ⟨Kbase, Cgain, hKbase, hCgain, ?_⟩
  intro M hs L n z omega eta heta hgood b epsilon hb hepsilon hepsilonHalf
    hparentOne theta htheta hnear k hk u hu ell hell
  have hetaRange : (1 / 32 : ℝ) ∈
      Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) := ⟨hs, by norm_num⟩
  have hcapIndicator := (hgoodCap M L (1 / 32 : ℝ) hetaRange eta heta n z omega).2
  have hmath : section6HomogenizationError M (1 / 32 : ℝ) L n omega z ≤
      C * eta := by
    simpa only [indicatorValue, ite_eq_left hgood] using hcapIndicator
  obtain ⟨hbaseParent, hbaseInner⟩ :=
    cutoffGoodEvent_parent_inner_paperError_le M L n z omega hC.le hs heta hgood hmath
  let alpha := tailCoefficientCubeAverage M L n (translatePotentialSample z omega)
  have halpha : 0 < alpha := tailCoefficientCubeAverage_pos M L n _
  have heta0 : 0 ≤ eta := by
    have : 0 ≤ (1 / 32 : ℝ)⁻¹ * M.delta ^ 2 := by positivity
    exact this.trans heta.1
  have hproductParent :=
    paperHomogenizationError_localizedTheta_toReal_le_goodScale
      M L (translatePotentialSample z omega) (measurableSet_openCubeSet (originCube d (n : ℤ)))
      (translatedMultiplier z theta) (continuousOn_translatedMultiplier htheta)
      hepsilon hepsilonHalf (translatedMultiplier_near_one hnear) halpha (by norm_num)
      heta0 heta.2 hKbase.le (originCube d (n : ℤ)) (n : ℤ) hbaseParent
  have hproductInner :=
    paperHomogenizationError_localizedTheta_toReal_le_goodScale
      M L (translatePotentialSample z omega) (measurableSet_openCubeSet (originCube d (n : ℤ)))
      (translatedMultiplier z theta) (continuousOn_translatedMultiplier htheta)
      hepsilon hepsilonHalf (translatedMultiplier_near_one hnear) halpha (by norm_num)
      heta0 heta.2 hKbase.le (originCube d ((n : ℤ) - 2)) ((n : ℤ) - 2) hbaseInner
  have hbaseParent' : paperHomogenizationError
      (originCube d (n : ℤ)) (n : ℤ) ((3 / 16 : ℝ) / 6)
      .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample z omega))
      alpha ≤ ENNReal.ofReal (productTwoScaleErrorFactor * C * eta) := by
    simpa only [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num, alpha] using hbaseParent
  have hbaseInner' : paperHomogenizationError
      (originCube d ((n : ℤ) - 2)) ((n : ℤ) - 2) ((3 / 16 : ℝ) / 6)
      .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample z omega))
      alpha ≤ ENNReal.ofReal (productTwoScaleErrorFactor * C * eta) := by
    simpa only [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num, alpha] using hbaseInner
  apply productTranslated_excessRecurrence_of_errorCap d M.shellPrefix.dimension
    M L omega theta (n : ℤ) z htheta hb hepsilon hepsilonHalf hnear halpha k hk
    u hu hbaseParent' hbaseInner'
  · simpa only [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num] using
      hproductParent.trans hparentOne
  · simpa only [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num,
      Kbase, Cgain] using hproductInner
  · exact hell

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
