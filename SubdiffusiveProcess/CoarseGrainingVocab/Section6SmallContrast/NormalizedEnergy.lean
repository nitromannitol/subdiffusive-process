module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.WeakTesting
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalPoincare

@[expose] public section

/-!
# Normalized Euclidean energy calculus for the small-contrast iteration
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Dictionary from the vector normalized energy to the Hilbert realization's
ordinary `L²` norm. -/
theorem vectorNormalizedL2On_eq_toReal_eLpNorm_div
    {W : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 W F) :
    vectorNormalizedL2On W F =
      (eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W)).toReal /
        Real.sqrt ((volume W).toReal) := by
  have hHF : MemLp (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField hF
  have hnorm : MemLp (fun x => euclideanNorm (F x)) 2 (volume.restrict W) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using! hHF.norm
  unfold vectorNormalizedL2On
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div
    hnorm]
  have hfun : (fun x => euclideanNorm (F x)) =
      fun x => ‖HilbertVec.ofVec (F x)‖ := by
    funext x
    exact euclideanNorm_eq_norm_ofVec (F x)
  rw [hfun, eLpNorm_norm _ hHF.aestronglyMeasurable]

/-- Raw and normalized Euclidean energies differ by the square root of the
window volume. -/
theorem sqrt_integral_vecNormSq_eq_sqrt_volume_mul_vectorNormalizedL2On
    {W : Set (Vec d)} {F : Vec d → Vec d}
    (hW : 0 < (volume W).toReal) (hF : MemVectorL2 W F) :
    Real.sqrt (∫ x in W, vecNormSq (F x) ∂volume) =
      Real.sqrt ((volume W).toReal) * vectorNormalizedL2On W F := by
  have hHF : MemLp (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField hF
  have hnorm : MemLp (fun x => euclideanNorm (F x)) 2 (volume.restrict W) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using! hHF.norm
  have hsq := Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hnorm
  have hnonneg : 0 ≤ (eLpNorm (fun x => euclideanNorm (F x)) 2
      (volume.restrict W)).toReal := ENNReal.toReal_nonneg
  have hsqrt : Real.sqrt (∫ x in W, vecNormSq (F x) ∂volume) =
      (eLpNorm (fun x => euclideanNorm (F x)) 2 (volume.restrict W)).toReal := by
    have hIntEq : (∫ x in W, vecNormSq (F x) ∂volume) =
        ∫ x in W, euclideanNorm (F x) ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact (euclideanNorm_sq (F x)).symm
    rw [hIntEq, ← hsq, Real.sqrt_sq hnonneg]
  rw [hsqrt, vectorNormalizedL2On_eq_toReal_eLpNorm_div hF]
  have hfun : (fun x => euclideanNorm (F x)) =
      fun x => ‖HilbertVec.ofVec (F x)‖ := by
    funext x
    exact euclideanNorm_eq_norm_ofVec _
  rw [hfun, eLpNorm_norm _ hHF.aestronglyMeasurable]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hW)]

/-- Minkowski for normalized Euclidean vector energy. -/
theorem vectorNormalizedL2On_add_le
    {W : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemVectorL2 W F) (hG : MemVectorL2 W G) :
    vectorNormalizedL2On W (fun x => F x + G x) ≤
      vectorNormalizedL2On W F + vectorNormalizedL2On W G := by
  have hHF : MemLp (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField hF
  have hHG : MemLp (fun x => HilbertVec.ofVec (G x)) 2 (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField hG
  have hsum : MemVectorL2 W (fun x => F x + G x) := hF.add hG
  have htri : eLpNorm (fun x => HilbertVec.ofVec (F x + G x)) 2
      (volume.restrict W) ≤
      eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) +
        eLpNorm (fun x => HilbertVec.ofVec (G x)) 2 (volume.restrict W) := by
    have heq : (fun x => HilbertVec.ofVec (F x + G x)) =
        (fun x => HilbertVec.ofVec (F x)) + fun x => HilbertVec.ofVec (G x) := by
      funext x
      exact (HilbertVec.ofVecL d).map_add (F x) (G x)
    rw [heq]
    exact eLpNorm_add_le one_le_two
  have hne : eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) +
      eLpNorm (fun x => HilbertVec.ofVec (G x)) 2 (volume.restrict W) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hHF.eLpNorm_ne_top, hHG.eLpNorm_ne_top⟩
  have hreal := ENNReal.toReal_mono hne htri
  rw [ENNReal.toReal_add hHF.eLpNorm_ne_top hHG.eLpNorm_ne_top] at hreal
  rw [vectorNormalizedL2On_eq_toReal_eLpNorm_div hsum,
    vectorNormalizedL2On_eq_toReal_eLpNorm_div hF,
    vectorNormalizedL2On_eq_toReal_eLpNorm_div hG, ← add_div]
  exact div_le_div_of_nonneg_right hreal (Real.sqrt_nonneg _)

/-- Triangle inequality in subtraction form. -/
theorem vectorNormalizedL2On_sub_le
    {W : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemVectorL2 W F) (hG : MemVectorL2 W G) :
    vectorNormalizedL2On W (fun x => F x - G x) ≤
      vectorNormalizedL2On W F + vectorNormalizedL2On W G := by
  have h := vectorNormalizedL2On_add_le hF hG.neg
  simpa [sub_eq_add_neg, euclideanNorm_neg, vectorNormalizedL2On,
    normalizedL2On] using! h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
