module

public import SubdiffusiveProcess.Paper.lfgc_p1_final

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Band family and witness hypotheses of the prefix cover

`lfgc_p1_final2` merges the two band-approximant families of lem_band into one family with a
common window width, rate and error constant; `lfgc_p1_final3` gives the measurability, error, window
and convergence hypotheses of the prefix witness for the approximants built from it.
-/

open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- One band-approximant family for both score tags. -/
theorem lfgc_p1_final2 [NeZero d] (M : GMCModel d) (Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ) (N : ℕ) (p : ℝ) {aZ aD cZ cD CpZ CpD Merr bf : ℝ}
    (wZ wD : ℕ) (hCpZ : 0 < CpZ) (_hCpD : 0 < CpD)
    (hsZ : bf * (CpZ * M.delta ^ cZ) ≤ Merr) (hsD : bf * (CpD * M.delta ^ cD) ≤ Merr)
    (hZ : ∀ (j : ℤ) (w : Vec d), j ≤ (N : ℤ) → ∀ h : ℕ, 1 ≤ h → ∃ Y : BilateralField d → ℝ,
      StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
        (Set.Icc (-j - (wZ * (h + 1) : ℕ)) (-j + (wZ * (h + 1) : ℕ)))] Y ∧
      eLpNorm (fun omega => aux_lfgc_sum_band_summand false Draw Z N j w omega - Y omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (CpZ * M.delta ^ cZ * (3 : ℝ) ^ (-(aZ * (h : ℝ)))))
    (hD : ∀ (j : ℤ) (w : Vec d), j ≤ (N : ℤ) → ∀ h : ℕ, 1 ≤ h → ∃ Y : BilateralField d → ℝ,
      StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
        (Set.Icc (-j - (wD * (h + 1) : ℕ)) (-j + (wD * (h + 1) : ℕ)))] Y ∧
      eLpNorm (fun omega => aux_lfgc_sum_band_summand true Draw Z N j w omega - Y omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (CpD * M.delta ^ cD * (3 : ℝ) ^ (-(aD * (h : ℝ)))))
    {a' : ℝ} (ha'Z : a' ≤ aZ) (ha'D : a' ≤ aD) (hδ : 0 < M.delta) :
    ∃ (Y : Bool → ℤ → Vec d → ℕ → BilateralField d → ℝ) (Eb : ℝ), 0 ≤ Eb ∧ bf * Eb ≤ Merr ∧
      (∀ b j w h, j ≤ (N : ℤ) → 1 ≤ h →
        StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
          (Set.Icc (-j - ((wZ + wD) * (h + 1) : ℕ)) (-j + ((wZ + wD) * (h + 1) : ℕ)))]
          (Y b j w h)) ∧
      (∀ b j w h, Measurable (Y b j w h)) ∧
      (∀ b j w h, j ≤ (N : ℤ) → 1 ≤ h →
        eLpNorm (fun omega => aux_lfgc_sum_band_summand b Draw Z N j w omega - Y b j w h omega)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Eb * (3 : ℝ) ^ (-(a' * h)))) := by
  obtain ⟨YZ, hYZ, hYZ0⟩ := aux_lfgc_p1_help_choose_family (N : ℤ) _ hZ
  obtain ⟨YD, hYD, hYD0⟩ := aux_lfgc_p1_help_choose_family (N : ℤ) _ hD
  have hEb0 : 0 ≤ max (CpZ * M.delta ^ cZ) (CpD * M.delta ^ cD) :=
    le_trans (by positivity) (le_max_left _ _)
  have hsub : ∀ (j : ℤ) (h ww : ℕ), ww ≤ wZ + wD →
      Set.Icc (-j - (ww * (h + 1) : ℕ)) (-j + (ww * (h + 1) : ℕ)) ⊆
        Set.Icc (-j - ((wZ + wD) * (h + 1) : ℕ)) (-j + ((wZ + wD) * (h + 1) : ℕ)) := by
    intro j h ww hww t ht
    have hle : ww * (h + 1) ≤ (wZ + wD) * (h + 1) := Nat.mul_le_mul_right _ hww
    have hle' : ((ww * (h + 1) : ℕ) : ℤ) ≤ (((wZ + wD) * (h + 1) : ℕ) : ℤ) := by exact_mod_cast hle
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hwin : ∀ b j w h, j ≤ (N : ℤ) → 1 ≤ h →
      StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
        (Set.Icc (-j - ((wZ + wD) * (h + 1) : ℕ)) (-j + ((wZ + wD) * (h + 1) : ℕ)))]
        ((fun b : Bool => cond b YD YZ) b j w h) := by
    intro b j w h hj hh
    cases b
    · exact (hYZ j w h hj hh).1.mono (layerWindow_mono (hsub j h wZ (by omega)))
    · exact (hYD j w h hj hh).1.mono (layerWindow_mono (hsub j h wD (by omega)))
  refine ⟨fun b : Bool => cond b YD YZ, max (CpZ * M.delta ^ cZ) (CpD * M.delta ^ cD), hEb0, ?_,
    hwin, ?_, ?_⟩
  · rcases le_total (CpZ * M.delta ^ cZ) (CpD * M.delta ^ cD) with h | h
    · rw [max_eq_right h]; exact hsD
    · rw [max_eq_left h]; exact hsZ
  · intro b j w h
    by_cases hc : j ≤ (N : ℤ) ∧ 1 ≤ h
    · exact ((hwin b j w h hc.1 hc.2).mono (layerWindow_le_pi _)).measurable
    · cases b
      · show Measurable (YZ j w h); rw [hYZ0 j w h hc]; exact measurable_const
      · show Measurable (YD j w h); rw [hYD0 j w h hc]; exact measurable_const
  · intro b j w h hj hh
    have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    cases b
    · refine (hYZ j w h hj hh).2.trans (ENNReal.ofReal_le_ofReal ?_)
      have h3 : (3 : ℝ) ^ (-(aZ * (h : ℝ))) ≤ (3 : ℝ) ^ (-(a' * h)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      exact mul_le_mul (le_max_left _ _) h3 (by positivity) hEb0
    · refine (hYD j w h hj hh).2.trans (ENNReal.ofReal_le_ofReal ?_)
      have h3 : (3 : ℝ) ^ (-(aD * (h : ℝ))) ≤ (3 : ℝ) ^ (-(a' * h)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      exact mul_le_mul (le_max_right _ _) h3 (by positivity) hEb0

end SubdiffusiveProcess.Paper
