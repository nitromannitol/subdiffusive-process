module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Static.HarmonicCellBallEstimate

@[expose] public section

/-! # Microscopic native data prices from an energy and a bounded forcing -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The source's real vector size is bounded by a pointwise Euclidean bound
and the exact volume factor. -/
theorem vectorLpSizeOn_le_of_bound {d : ℕ} (W : Set (Vec d)) (hW : MeasurableSet W)
    (hWfin : volume W ≠ ⊤) (p : ℝ) (F : Vec d → Vec d) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ W, euclideanNorm (F x) ≤ B) :
    vectorLpSizeOn W p F ≤ (volume W).toReal ^ ((ENNReal.ofReal p).toReal)⁻¹ * B := by
  have hnorm : SubdiffusiveProcess.RawLp.eLpNorm (fun x => euclideanNorm (F x)) (ENNReal.ofReal p)
      (volume.restrict W) ≤ (volume W) ^ ((ENNReal.ofReal p).toReal)⁻¹ * ENNReal.ofReal B := by
    calc
      _ ≤ SubdiffusiveProcess.RawLp.eLpNorm (fun _ : Vec d => B) (ENNReal.ofReal p)
          (volume.restrict W) := by
        apply SubdiffusiveProcess.RawLp.eLpNorm_mono_ae
        filter_upwards [ae_restrict_mem hW] with x hx
        simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _),
          abs_of_nonneg hB] using! hbound x hx
      _ = eLpNorm (fun _ : Vec d => B) (ENNReal.ofReal p) (volume.restrict W) :=
        SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded aestronglyMeasurable_const
      _ ≤ _ := by
        simpa only [Measure.restrict_apply_univ] using!
          (eLpNorm_le_of_ae_bound (p := ENNReal.ofReal p)
            (μ := volume.restrict W) (f := fun _ : Vec d => B)
            aestronglyMeasurable_const (Filter.Eventually.of_forall fun _ => by
              simp only [Real.norm_eq_abs, abs_of_nonneg hB]
              exact le_rfl))
  have hfin : (volume W) ^ ((ENNReal.ofReal p).toReal)⁻¹ * ENNReal.ofReal B ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hWfin) ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono hfin hnorm
  simpa only [vectorLpSizeOn, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hB] using h

/-- A physical energy budget and a bounded physical forcing control the
complete unit-ball data price, including its finite source exponent. -/
theorem smallContrastDataSize_ballToUnit_le {d : ℕ} [NeZero d]
    (z : Vec d) {rho kappa E T : ℝ} (hrho : 0 < rho) (hkappa : 0 < kappa)
    (u : H1Function (euclideanBall z rho)) (F : Vec d → Vec d)
    (hE : ∫ x in euclideanBall z rho, vecNormSq (u.grad x) ≤ E)
    (hT : 0 ≤ T) (hF : ∀ x ∈ euclideanBall z rho, euclideanNorm (F x) ≤ T) :
    smallContrastDataSize d (3 / 4 : ℝ) (ballToUnitH1 z hrho u)
        (ballToUnitSource F z rho kappa) ≤
      Real.sqrt ((rho ^ d)⁻¹ * E) + 4 *
        (volume (smallContrastUnitBall d)).toReal ^
          ((ENNReal.ofReal (schauderSourceExponent d (3 / 4 : ℝ))).toReal)⁻¹ *
        (kappa⁻¹ * T) := by
  have hsource : vectorLpSizeOn (smallContrastUnitBall d)
      (schauderSourceExponent d (3 / 4 : ℝ)) (ballToUnitSource F z rho kappa) ≤
      (volume (smallContrastUnitBall d)).toReal ^
        ((ENNReal.ofReal (schauderSourceExponent d (3 / 4 : ℝ))).toReal)⁻¹ * (kappa⁻¹ * T) := by
    apply vectorLpSizeOn_le_of_bound _ (isOpen_euclideanBall (0 : Vec d) 1).measurableSet
      (Homogenization.Book.Ch01.volume_euclideanBall_ne_top 0 1) _ _ (by positivity)
    intro y hy
    have hfy := hF _ ((affine_mem_euclideanBall_iff_of_pos z y hrho).2 hy)
    simp only [ballToUnitSource, euclideanNorm_smul, abs_of_pos (inv_pos.mpr hkappa)]
    exact mul_le_mul_of_nonneg_left hfy (inv_nonneg.mpr hkappa.le)
  unfold smallContrastDataSize
  rw [vectorLpSizeOn_two_ballToUnit_grad_eq hrho]
  norm_num only
  calc
    _ ≤ Real.sqrt ((rho ^ d)⁻¹ * E) + 4 *
        ((volume (smallContrastUnitBall d)).toReal ^
          ((ENNReal.ofReal (schauderSourceExponent d (3 / 4 : ℝ))).toReal)⁻¹ * (kappa⁻¹ * T)) := by
      apply add_le_add
      · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE (by positivity))
      · exact mul_le_mul_of_nonneg_left hsource (by norm_num)
    _ = _ := by ring

end SubdiffusiveProcess.Static
