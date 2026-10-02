import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicHalfMeasureLower
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicScaling
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicLogSquare
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicValues

/-! # An essential lower bound from a half-measure set -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A dimensional lower bound on the eighth cube, obtained from a
half-measure set on the half cube. All constants precede the coefficient
and the solution. -/
theorem exists_essential_harmonic_half_measure_lower {d : ℕ} (hd : 2 ≤ d) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 4 ∧
      ∀ (a : Vec d → ℝ) (z : Vec d),
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
      ∀ h : H1Function (centeredAxisCube z 1), IsWeaklyHarmonicOn a (centeredAxisCube z 1) h →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 0 ≤ h.toFun x ∧ h.toFun x ≤ 1) →
      ∀ E : Set (Vec d),
      (volume (centeredAxisCube z (1 / 2))).toReal / 2 ≤
        ((volume.restrict (centeredAxisCube z (1 / 2))) E).toReal →
      (∀ᵐ x ∂(volume.restrict (centeredAxisCube z (1 / 2))).restrict E, 1 / 2 ≤ h.toFun x) →
      ∀ᵐ x ∂volume.restrict (centeredAxisCube z (1 / 8)), delta / 2 ≤ h.toFun x := by
  obtain ⟨B, hB, hmoser⟩ := exists_essential_harmonic_scaled_positive_bound hd
  obtain ⟨C, hC, hlogSquare⟩ := exists_essential_harmonic_log_square d
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
  intro a z hab ha h hh hh01 E hhalf hgood
  let Q := centeredAxisCube z (1 / 2)
  let mu := volume.restrict Q
  have hQsub : Q ⊆ centeredAxisCube z 1 := centeredAxisCube_mono (by norm_num)
  have hQopen : IsOpen Q := isOpen_axisCube _ _
  letI : IsFiniteMeasure (volume.restrict Q) :=
    (isOpenBoundedConvexDomain_axisCube (fun i => z i - (1 / 2) / 2) (1 / 2)).isFiniteMeasure_restrict_volume
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
  have h01 := hh01.filter_mono (ae_mono (Measure.restrict_mono hQsub le_rfl))
  have hh0 : ∀ᵐ y ∂mu, 0 ≤ h.toFun y := h01.mono fun _ hx => hx.1
  have hnorm := harmonic_positive_part_norm_le_log hh0 hdelta hT hlog hu
  have hnorm' : eLpNorm (fun y => max (delta - h.toFun y) 0) 2 mu ≤
      ENNReal.ofReal (delta / T) * (ENNReal.ofReal (Real.sqrt C) * volume Q ^ (1 / 2 : ℝ)) :=
    hnorm.trans (mul_le_mul' le_rfl hunorm)
  let hQ := h.restrict hQopen hQsub
  let g := ((-1 : ℝ) • hQ).addConst delta
  have hg : IsWeaklyHarmonicOn a Q g := essential_harmonic_affine hQ
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict
      (isOpen_axisCube _ _) hQopen hQsub hh) (-1) delta
  have hgf : g.toFun = fun y => delta - h.toFun y := by
    funext y
    change (-1 : ℝ) * h.toFun y + delta = _
    ring
  have hgb : ∀ᵐ y ∂volume.restrict Q, |g.toFun y| ≤ delta + 1 := by
    filter_upwards [h01] with y hy
    rw [hgf]
    apply abs_le.mpr
    constructor <;> linarith
  have hag : AEStronglyMeasurable a (volume.restrict Q) := ha.mono_set hQsub
  have habg := hab.filter_mono (ae_mono (Measure.restrict_mono hQsub le_rfl))
  have hm := hmoser a z (1 / 2) (by norm_num) habg hag g hg (delta + 1)
    (by positivity) hgb
  rw [hgf, show ((1 / 2 : ℝ) / 4) = 1 / 8 by norm_num] at hm
  filter_upwards [hm] with x hmx
  have hpoint : ENNReal.ofReal (max (delta - h.toFun x) 0) ≤ ENNReal.ofReal (delta / 2) := by
    calc
      _ ≤ ENNReal.ofReal B * volume Q ^ (-(1 / 2) : ℝ) *
          eLpNorm (fun y => max (delta - h.toFun y) 0) 2 mu := hmx
      _ ≤ ENNReal.ofReal B * volume Q ^ (-(1 / 2) : ℝ) *
          (ENNReal.ofReal (delta / T) * (ENNReal.ofReal (Real.sqrt C) * volume Q ^ (1 / 2 : ℝ))) :=
        mul_le_mul' le_rfl hnorm'
      _ = ENNReal.ofReal B * ENNReal.ofReal (delta / T) * ENNReal.ofReal (Real.sqrt C) :=
        harmonic_log_mass_cancellation hM0 hMtop _ _ _
      _ = ENNReal.ofReal (B * (delta / T) * Real.sqrt C) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hB.le]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hprice
  have hp := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ delta / 2)).mp hpoint
  linarith [le_max_left (delta - h.toFun x) 0]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
