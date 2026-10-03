module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalCaccioppoliReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.BallForcing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum

@[expose] public section

/-!
# Endpoint prices for the local Caccioppoli datum

Multiplication by the physical radius cancels the inverse-radius and
normalized-volume factors in the Caccioppoli datum.  This is the elementary
scale-invariant estimate used by the direct nonpositive-scale branch.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- Dimension-only price after the radius cancellation in the explicit
Caccioppoli datum. -/
def boundedMultiplierCaccioppoliEndpointConst (d : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ d *
    (16 * (d : ℝ) * quantitativeBallCutoffGradientConst d ^ 2) *
      (volume (smallContrastUnitBall d)).toReal)

theorem boundedMultiplierCaccioppoliEndpointConst_nonneg (d : ℕ) :
    0 ≤ boundedMultiplierCaccioppoliEndpointConst d :=
  Real.sqrt_nonneg _

/-- If the centered function is bounded almost everywhere on the outer ball,
then the Caccioppoli datum times the half-radius is bounded by a
dimension-only multiple of that pointwise bound. -/
theorem halfBallCaccioppoliDataPrice_mul_halfRadius_le_of_ae_abs_le
    [NeZero d] {x : Vec d} {R O : ℝ} (hR : 0 < R) (hO : 0 ≤ O)
    {f : Vec d → ℝ} (c : ℝ)
    (hint : IntegrableOn (fun y ↦ (f y - c) ^ 2) (euclideanBall x R))
    (hbound : ∀ᵐ y ∂volume.restrict (euclideanBall x R),
      |f y - c| ≤ O) :
    halfBallCaccioppoliDataPrice d x R f c * (R / 2) ≤
      boundedMultiplierCaccioppoliEndpointConst d * O := by
  let V := (volume (euclideanBall x R)).toReal
  have hV : V = (volume (smallContrastUnitBall d)).toReal * R ^ d := by
    dsimp only [V]
    exact volume_euclideanBall_toReal_eq_unit_mul_pow x hR
  have hVtop : volume (euclideanBall x R) ≠ ⊤ :=
    Homogenization.Book.Ch01.volume_euclideanBall_ne_top x R
  have hconst : IntegrableOn (fun _ : Vec d ↦ O ^ 2) (euclideanBall x R) :=
    integrableOn_const hVtop
  have hintLe : (∫ y in euclideanBall x R, (f y - c) ^ 2) ≤ V * O ^ 2 := by
    have hmono : (∫ y in euclideanBall x R, (f y - c) ^ 2) ≤
        ∫ _y in euclideanBall x R, O ^ 2 := by
      refine setIntegral_mono_ae_restrict hint hconst ?_
      filter_upwards [hbound] with y hy
      exact sq_le_sq' (neg_le_of_abs_le hy) (le_of_abs_le hy)
    rw [setIntegral_const, measureReal_def, smul_eq_mul] at hmono
    simpa only [V] using hmono
  have hfactor0 : 0 ≤ ((R / 2) ^ d)⁻¹ *
      ((16 * (d : ℝ) *
        (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
        ∫ y in euclideanBall x R, (f y - c) ^ 2) := by
    positivity
  have hfactorLe : ((R / 2) ^ d)⁻¹ *
      ((16 * (d : ℝ) *
        (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
        ∫ y in euclideanBall x R, (f y - c) ^ 2) ≤
      ((R / 2) ^ d)⁻¹ *
      ((16 * (d : ℝ) *
        (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
        (V * O ^ 2)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hintLe (by positivity)) (by positivity)
  have hsqrt := Real.sqrt_le_sqrt hfactorLe
  have hhalf : 0 ≤ R / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hsqrt hhalf
  change Real.sqrt (((R / 2) ^ d)⁻¹ *
        ((16 * (d : ℝ) *
          (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
          ∫ y in euclideanBall x R, (f y - c) ^ 2)) * (R / 2) ≤
      boundedMultiplierCaccioppoliEndpointConst d * O
  refine hscaled.trans_eq ?_
  have hendpoint0 : 0 ≤ (2 : ℝ) ^ d *
      (16 * (d : ℝ) * quantitativeBallCutoffGradientConst d ^ 2) *
        (volume (smallContrastUnitBall d)).toReal := by positivity
  have hfactorBound0 : 0 ≤ ((R / 2) ^ d)⁻¹ *
      ((16 * (d : ℝ) *
        (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
        (V * O ^ 2)) := by positivity
  have hsqrtHalf : Real.sqrt ((R / 2) ^ 2) = R / 2 :=
    Real.sqrt_sq hhalf
  calc
    Real.sqrt (((R / 2) ^ d)⁻¹ *
          ((16 * (d : ℝ) *
            (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
            (V * O ^ 2))) * (R / 2) =
        Real.sqrt (((R / 2) ^ d)⁻¹ *
          ((16 * (d : ℝ) *
            (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
            (V * O ^ 2))) * Real.sqrt ((R / 2) ^ 2) := by rw [hsqrtHalf]
    _ = Real.sqrt ((((R / 2) ^ d)⁻¹ *
          ((16 * (d : ℝ) *
            (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
            (V * O ^ 2))) * (R / 2) ^ 2) := by
      rw [Real.sqrt_mul hfactorBound0]
    _ = Real.sqrt (((2 : ℝ) ^ d *
          (16 * (d : ℝ) * quantitativeBallCutoffGradientConst d ^ 2) *
            (volume (smallContrastUnitBall d)).toReal) * O ^ 2) := by
      congr 1
      rw [hV]
      have hRne : R ≠ 0 := hR.ne'
      rw [show R - R / 2 = R / 2 by ring, div_pow]
      field_simp [hRne]
    _ = Real.sqrt ((2 : ℝ) ^ d *
          (16 * (d : ℝ) * quantitativeBallCutoffGradientConst d ^ 2) *
            (volume (smallContrastUnitBall d)).toReal) * O := by
      rw [Real.sqrt_mul hendpoint0, Real.sqrt_sq hO]
    _ = boundedMultiplierCaccioppoliEndpointConst d * O := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
