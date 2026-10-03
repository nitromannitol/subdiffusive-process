module

public import SubdiffusiveProcess.Paper.lfgc_p_trunc_conv

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `L^p` remainder of the truncated field score

For a sample family `eta` with the canonical formula almost surely, the field score formula
and its truncation at depth `H` differ in `L^p` by at most `3^{-sH/16}` times the `L^{2⌈p⌉}`
bound of the half-discount bank series, uniformly in the cutoff, the level and the centre.
-/

open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p_trunc_lp_f_field_term_le_half (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (y : Vec d) (g : PotentialSample d)
    (j : ℕ) :
    Paper.aux_lem_band_piece_field_term s n y g j ≤
      Paper.aux_lem_band_piece_field_term (s / 2) n y g j := by
  unfold Paper.aux_lem_band_piece_field_term
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h : (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) ≤ (3 : ℝ) ^ (-(s / 2 * (j : ℝ) / 8)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal h) _

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p_trunc_lp_f_ffull_le_bank (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    aux_lfgc_p_trunc_ffull s n y g ≤ ∑' j : ℕ, Paper.prefix_bank_Fmaj (s / 2) n y j g := by
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  exact ((aux_lfgc_p_trunc_lp_f_field_term_le_half s hs n y g j).trans
    (Paper.aux_lem_band_piece_field_term_le_bank (s / 2) n j y g)).trans (ENNReal.le_tsum (f := fun j => Paper.prefix_bank_Fmaj (s / 2) n y j g) j)

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p_trunc_lp_f_ffull_le_ftr_add (s : ℝ) (hs : 0 < s) (n : ℕ) (y : Vec d) (H : ℕ)
    (g : PotentialSample d) :
    aux_lfgc_p_trunc_ffull s n y g ≤ aux_lfgc_p_trunc_ftr s n y H g +
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (H : ℝ) / 16))) *
        ∑' j : ℕ, Paper.prefix_bank_Fmaj (s / 2) n y j g := by
  have h := Paper.aux_lem_band_piece_field_tail_dominance s hs
    (fun j => ∑ i ∈ Finset.Icc (n - j) (n + j),
      Paper.aux_lem_band_piece_field_normOn (translatedCube d (n + 1 + j) y)
        (fun x : Vec d => |g i x| + (3 : ℝ) ^ (i : ℝ) *
          Homogenization.euclideanNorm (shellGradient (g i) x))) H
  refine h.trans (add_le_add le_rfl (mul_le_mul_right ?_ _))
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  exact (Paper.aux_lem_band_piece_field_term_le_bank (s / 2) n j y g).trans (ENNReal.le_tsum (f := fun j => Paper.prefix_bank_Fmaj (s / 2) n y j g) j)

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p_trunc_lp_f_ftr_le_ffull (s : ℝ) (n : ℕ) (y : Vec d) (H : ℕ) (g : PotentialSample d) :
    aux_lfgc_p_trunc_ftr s n y H g ≤ aux_lfgc_p_trunc_ffull s n y g := by
  rw [← aux_lfgc_p_trunc_conv_iSup_ftr]
  exact le_iSup (fun L => aux_lfgc_p_trunc_ftr s n y L g) H

/-- Uniform `L^p` remainder of the truncated field score. -/
theorem lfgc_p_trunc_lp_f (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N n : ℕ) (w : Vec d) (H : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun omega => (aux_lfgc_p_trunc_ffull s n w (eta N omega)).toReal - (aux_lfgc_p_trunc_ftr s n w H (eta N omega)).toReal)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (H : ℝ) / 16))) *
        ENNReal.ofReal (∑' j : ℕ, Paper.prefix_even_series_bound M (s / 2) ⌈p⌉₊ j) := by
  set μ := (chaosSampleLaw M).toMeasure
  have half_pos : (0 : ℝ) < s / 2 := by linarith
  set qnat : ℕ := ⌈p⌉₊ with hqnat
  have hqnat1 : 1 ≤ qnat := Nat.ceil_pos.mpr (by linarith)
  have hmeasEta := Paper.prefix_eta_aemeasurable M eta hEta N
  set B : BilateralField d → ℝ≥0∞ := fun omega =>
    ∑' j : ℕ, Paper.prefix_bank_Fmaj (s / 2) n w j (eta N omega) with hB
  have hBfin : ∀ᵐ omega ∂μ, B omega ≠ ⊤ := by
    have hpush : ∀ᵐ g ∂Measure.map (eta N) μ,
        (∑' j : ℕ, Paper.prefix_bank_Fmaj (s / 2) n w j g) ≠ ⊤ := by
      rw [Paper.prefix_eta_law M eta hEta N]
      exact Paper.prefix_bank_Fmaj_tsum_ae M (s / 2) half_pos n w
    exact ae_of_ae_map hmeasEta hpush
  have hrate : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (H : ℝ) / 16)) := Real.rpow_nonneg (by norm_num) _
  have hpoint : ∀ᵐ omega ∂μ,
      ‖(aux_lfgc_p_trunc_ffull s n w (eta N omega)).toReal - (aux_lfgc_p_trunc_ftr s n w H (eta N omega)).toReal‖ ≤
        (3 : ℝ) ^ (-(s * (H : ℝ) / 16)) * ‖(B omega).toReal‖ := by
    filter_upwards [hBfin] with omega hBo
    have hF := aux_lfgc_p_trunc_lp_f_ffull_le_bank s hs.le n w (eta N omega)
    have hFfin : aux_lfgc_p_trunc_ffull s n w (eta N omega) ≠ ⊤ := ne_top_of_le_ne_top hBo hF
    have hT := aux_lfgc_p_trunc_lp_f_ftr_le_ffull s n w H (eta N omega)
    have hTfin : aux_lfgc_p_trunc_ftr s n w H (eta N omega) ≠ ⊤ := ne_top_of_le_ne_top hFfin hT
    have hup := aux_lfgc_p_trunc_lp_f_ffull_le_ftr_add s hs n w H (eta N omega)
    have hmul : ENNReal.ofReal ((3 : ℝ) ^ (-(s * (H : ℝ) / 16))) * B omega ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBo
    have hup' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hTfin, hmul⟩) hup
    rw [ENNReal.toReal_add hTfin hmul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hrate] at hup'
    have hlo := ENNReal.toReal_mono hFfin hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg ENNReal.toReal_nonneg]
    linarith
  have hfullMeas : Measurable (aux_lfgc_p_trunc_ffull s n w) := by
    have heq : aux_lfgc_p_trunc_ffull s n w =
        (fun g => ⨆ L, aux_lfgc_p_trunc_ftr s n w L g) := by
      funext g
      exact (aux_lfgc_p_trunc_conv_iSup_ftr s n w g).symm
    rw [heq]
    exact Measurable.iSup (fun L => aux_lfgc_p_trunc_measurable_ftr s n w L)
  have hdiffMeas : AEStronglyMeasurable (fun omega =>
      (aux_lfgc_p_trunc_ffull s n w (eta N omega)).toReal -
      (aux_lfgc_p_trunc_ftr s n w H (eta N omega)).toReal) μ :=
    (ENNReal.measurable_toReal.comp_aemeasurable
      (hfullMeas.comp_aemeasurable hmeasEta)).aestronglyMeasurable.sub
      (ENNReal.measurable_toReal.comp_aemeasurable
        ((aux_lfgc_p_trunc_measurable_ftr s n w H).comp_aemeasurable
          hmeasEta)).aestronglyMeasurable
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdiffMeas hpoint (ENNReal.ofReal p)
  have hBmeas : AEStronglyMeasurable (fun omega => (B omega).toReal) μ :=
    (ENNReal.measurable_toReal.comp_aemeasurable (AEMeasurable.ennreal_tsum fun j =>
      (Paper.prefix_bank_Fmaj_measurable (s / 2) n w j).comp_aemeasurable hmeasEta)).aestronglyMeasurable
  have h2qnat : ENNReal.ofReal p ≤ ((2 * qnat : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Nat.le_ceil p
    push_cast
    linarith
  have hcongr : (fun omega => (B omega).toReal) =ᵐ[μ]
      (fun omega => ∑' j : ℕ, Paper.prefix_real_Fmaj (s / 2) n w j (eta N omega)) := by
    filter_upwards [hBfin] with omega hom
    rw [hB]
    simp only
    rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.ne_top_of_tsum_ne_top hom j)]
    congr 1
    funext j
    exact Paper.prefix_bank_Fmaj_toReal_eq (s / 2) n w j (eta N omega)
  have h2 : eLpNorm (fun omega => (B omega).toReal) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (∑' j : ℕ, Paper.prefix_even_series_bound M (s / 2) qnat j) := by
    calc eLpNorm (fun omega => (B omega).toReal) (ENNReal.ofReal p) μ
        ≤ eLpNorm (fun omega => (B omega).toReal) ((2 * qnat : ℕ) : ℝ≥0∞) μ :=
          eLpNorm_le_eLpNorm_of_exponent_le h2qnat
      _ = eLpNorm (fun omega => ∑' j : ℕ, Paper.prefix_real_Fmaj (s / 2) n w j (eta N omega))
            ((2 * qnat : ℕ) : ℝ≥0∞) μ := eLpNorm_congr_ae hcongr
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (Paper.prefix_even_series_bound M (s / 2) qnat j) :=
          Paper.prefix_eta_real_Fmaj_tsum_eLpNorm_even M (s / 2) half_pos eta hEta N n w qnat
            hqnat1
      _ = ENNReal.ofReal (∑' j : ℕ, Paper.prefix_even_series_bound M (s / 2) qnat j) :=
          (ENNReal.ofReal_tsum_of_nonneg (Paper.prefix_even_series_bound_nonneg M (s / 2) qnat)
            (Paper.prefix_even_series_bound_summable M (s / 2) half_pos qnat)).symm
  calc eLpNorm (fun omega => (aux_lfgc_p_trunc_ffull s n w (eta N omega)).toReal -
        (aux_lfgc_p_trunc_ftr s n w H (eta N omega)).toReal) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (H : ℝ) / 16))) *
          eLpNorm (fun omega => (B omega).toReal) (ENNReal.ofReal p) μ := h1
    _ ≤ _ := mul_le_mul_right h2 _

end Paper
