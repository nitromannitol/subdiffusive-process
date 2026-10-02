import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicLogSquare
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicLogLevel
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicScaledBoundedness
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicValueOperations

/-!
# A lower bound from a half-measure set

Logarithmic square control and positive-part Moser boundedness turn a
half-measure set above `1/2` into a dimensional positive lower bound.
The regularization is chosen explicitly; no limiting representative is used.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Cancellation of the exact volume normalization in the logarithmic
positive-part estimate. -/
theorem harmonic_log_mass_cancellation {M : ℝ≥0∞}
    (hM0 : M ≠ 0) (hMtop : M ≠ ⊤) (B c K : ℝ≥0∞) :
    B * M ^ (-(1 / 2) : ℝ) * (c * (K * M ^ (1 / 2 : ℝ))) = B * c * K := by
  calc
    _ = B * c * K * (M ^ (-(1 / 2) : ℝ) * M ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by
      rw [← ENNReal.rpow_add _ _ hM0 hMtop]
      norm_num

/-- A dimensional lower bound on the eighth cube, obtained from a
half-measure set on the half cube. All constants precede the coefficient
and the solution. -/
theorem exists_harmonic_unit_half_measure_lower {d : ℕ} (hd : 2 ≤ d) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 4 ∧
      ∀ (a : Vec d → ℝ) (z : Vec d),
      (∀ x ∈ centeredAxisCube z 1, 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (centeredAxisCube z 1) h →
      (∀ x ∈ centeredAxisCube z 1, 0 ≤ h x ∧ h x ≤ 1) →
      ∀ E : Set (Vec d),
      (volume (centeredAxisCube z (1 / 2))).toReal / 2 ≤
        ((volume.restrict (centeredAxisCube z (1 / 2))) E).toReal →
      (∀ᵐ x ∂(volume.restrict (centeredAxisCube z (1 / 2))).restrict E, 1 / 2 ≤ h x) →
      ∀ x ∈ centeredAxisCube z (1 / 8), delta / 2 ≤ h x := by
  obtain ⟨B, hB, hmoser⟩ := exists_harmonic_scaled_positive_bound hd
  obtain ⟨C, hC, hlogSquare⟩ := exists_harmonic_unit_log_square d
  let T : ℝ := 2 * B * Real.sqrt C + 2
  have hT : 0 < T := by dsimp only [T]; positivity
  have hT2 : 2 ≤ T := by
    have : 0 ≤ 2 * B * Real.sqrt C := by positivity
    dsimp only [T]
    linarith
  let delta : ℝ := Real.exp (-T) / 2
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdelta1 : delta ≤ 1 / 4 := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hexp : Real.exp (-T) ≤ (2 : ℝ)⁻¹ := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      linarith
    dsimp only [delta]
    norm_num at hexp ⊢
    linarith
  have hlog : Real.log (2 * delta) = -T := by
    rw [show 2 * delta = Real.exp (-T) by dsimp only [delta]; ring, Real.log_exp]
  have hprice : B * (delta / T) * Real.sqrt C ≤ delta / 2 := by
    have hBT : B * Real.sqrt C ≤ T / 2 := by dsimp only [T]; linarith
    calc
      B * (delta / T) * Real.sqrt C = (delta / T) * (B * Real.sqrt C) := by ring
      _ ≤ (delta / T) * (T / 2) := mul_le_mul_of_nonneg_left hBT (by positivity)
      _ = delta / 2 := by field_simp
  refine ⟨delta, hdelta, hdelta1, ?_⟩
  intro a z hab ha h hh hh01 E hhalf hgood x hx
  let Q := centeredAxisCube z (1 / 2)
  let mu := volume.restrict Q
  have hQsub : Q ⊆ centeredAxisCube z 1 := centeredAxisCube_mono (by norm_num)
  have hQopen : IsOpen Q := isOpen_axisCube _ _
  have hM : mu Set.univ = volume Q := by simp only [mu, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hM0 : volume Q ≠ 0 := by
    rw [volume_centeredAxisCube_eq z (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    positivity
  have hMtop : volume Q ≠ ⊤ := by
    rw [volume_centeredAxisCube_eq z (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact ENNReal.ofReal_ne_top
  obtain ⟨u, hu, husq⟩ := hlogSquare a z hab ha h hh hh01 E hhalf hgood delta hdelta hdelta1
  have hunorm := harmonic_eLpNorm_two_le_sqrt_mass (mu := mu) u.memL2
    (hM.symm ▸ hM0) (hM.symm ▸ hMtop) hC.le (by simpa only [hM] using husq)
  rw [hM] at hunorm
  have hh0 : ∀ᵐ y ∂mu, 0 ≤ h y := by
    filter_upwards [ae_restrict_mem hQopen.measurableSet] with y hy
    exact (hh01 y (hQsub hy)).1
  have hnorm := harmonic_positive_part_norm_le_log hh0 hdelta hT hlog hu
  have hnorm' : eLpNorm (fun y => max (delta - h y) 0) 2 mu ≤
      ENNReal.ofReal (delta / T) * (ENNReal.ofReal (Real.sqrt C) * volume Q ^ (1 / 2 : ℝ)) :=
    hnorm.trans (mul_le_mul' le_rfl hunorm)
  have hg : WeakHarmonic a Q (fun y => delta - h y) := by
    convert harmonic_weakHarmonic_affine_value (moser_weakHarmonic_mono hh hQsub) (-1) delta using 1
    ext y
    ring
  have hag : AEStronglyMeasurable a (volume.restrict Q) := ha.mono_set hQsub
  have hm := hmoser a z (1 / 2) (by norm_num) (fun y hy => hab y (hQsub hy)) hag
    (fun y => delta - h y) hg x (by convert hx using 1; norm_num)
  have hpoint : ENNReal.ofReal (max (delta - h x) 0) ≤ ENNReal.ofReal (delta / 2) := by
    calc
      _ ≤ ENNReal.ofReal B * volume Q ^ (-(1 / 2) : ℝ) *
          eLpNorm (fun y => max (delta - h y) 0) 2 mu := hm
      _ ≤ ENNReal.ofReal B * volume Q ^ (-(1 / 2) : ℝ) *
          (ENNReal.ofReal (delta / T) * (ENNReal.ofReal (Real.sqrt C) * volume Q ^ (1 / 2 : ℝ))) :=
        mul_le_mul' le_rfl hnorm'
      _ = ENNReal.ofReal B * ENNReal.ofReal (delta / T) * ENNReal.ofReal (Real.sqrt C) :=
        harmonic_log_mass_cancellation hM0 hMtop _ _ _
      _ = ENNReal.ofReal (B * (delta / T) * Real.sqrt C) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hB.le]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hprice
  have hp := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ delta / 2)).mp hpoint
  linarith [le_max_left (delta - h x) 0]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
