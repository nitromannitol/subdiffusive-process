import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SandwichNondegeneracyAttainment
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RepresentativeReadout
import Homogenization.Geometry.Translation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Boundedness and affine transport for normalized quadratic oscillation.
These identities and inequalities do not supply regularity of solutions. -/
open MeasureTheory Set SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal Pointwise
namespace SubdiffusiveProcess

/-- Essential boundedness bounds the normalized quadratic oscillation by the same constant. -/
theorem normalizedOscillation_le_of_ae_bound {d : ℕ} {W : Set (Vec d)}
    (hW : MeasurableSet W) (hpos : 0 < (volume W).toReal) (hfin : volume W ≠ ⊤)
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume.restrict W)) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂volume.restrict W,|f x| ≤ M) :
    normalizedL2On W (fun x => f x-averageOn W f) ≤ M := by
  haveI hfinite : IsFiniteMeasure (volume.restrict W) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hf2 : IntegrableOn (fun x => f x^2) W := hf.integrable_sq
  have hmean := Section6Iteration.normalizedL2On_sub_volumeAverage_le hW hpos hfin
    (hf.integrable (by norm_num)) hf2 0
  simp only [sub_zero] at hmean
  apply hmean.trans
  apply Section6Iteration.normalizedL2On_le_of_sq_le hM
  have hint : (∫ x in W,f x^2) ≤ (volume W).toReal*M^2 := by
    have hh := integral_mono_ae hf2 (integrable_const (M^2)) (hbound.mono fun x hx => by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f x)) hx 2)
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] using hh
  unfold volumeAverage
  have hh := mul_le_mul_of_nonneg_left hint (inv_pos.mpr hpos).le
  simpa only [← mul_assoc,inv_mul_cancel₀ hpos.ne',one_mul] using hh

/-- Positive affine changes of coordinates preserve normalized averages. -/
theorem volumeAverage_affine {d : ℕ} (s : ℝ) (hs : 0 < s) (z : Vec d)
    (W : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage (translateSet z (s • W)) f = volumeAverage W (fun y => f (s • y+z)) := by
  unfold volumeAverage
  rw [volume_translateSet_eq,← setIntegral_comp_addRight_translateSet]
  have hint := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Vec d))
    (fun y => f (y+z)) W hs
  rw [Module.finrank_fin_fun,smul_eq_mul] at hint
  rw [Measure.addHaar_smul,Module.finrank_fin_fun,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _),abs_of_pos (pow_pos hs d),mul_inv]
  rw [mul_comm ((s^d)⁻¹),mul_assoc,← hint]

/-- Positive affine changes of coordinates preserve normalized quadratic oscillation. -/
theorem normalizedOscillation_affine {d : ℕ} (s : ℝ) (hs : 0 < s) (z : Vec d)
    (W : Set (Vec d)) (f : Vec d → ℝ) :
    normalizedL2On (translateSet z (s • W))
      (fun x => f x-averageOn (translateSet z (s • W)) f) =
    normalizedL2On W (fun y => f (s • y+z)-averageOn W (fun y => f (s • y+z))) := by
  change Real.sqrt (volumeAverage (translateSet z (s • W))
    (fun x => (f x-volumeAverage (translateSet z (s • W)) f)^2)) = _
  rw [volumeAverage_affine s hs z W f,volumeAverage_affine s hs z W]
  rfl

end SubdiffusiveProcess
