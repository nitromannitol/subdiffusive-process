module

public import SubdiffusiveProcess.Paper.lfgc_p_trunc_lp_d

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `L^p` remainders of the truncated bad and drift scores

For a sample family with the canonical formula almost surely and small disorder, the bad score
formula and its truncation at depth `H` differ in `L^p` by at most `C 3^{-sH/32}`, and the drift
score formula and its truncation by at most `C 3^{-H}`, with `C` independent of the cutoff, the
level, the centre and `H`.
-/

open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_p_trunc_lp_ffull_ae_finite (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N n : ℕ) (w : Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, aux_lfgc_p_trunc_ffull s n w (eta N omega) ≠ ⊤ := by
  have half_pos : (0 : ℝ) < s / 2 := by linarith
  have hpush : ∀ᵐ g ∂Measure.map (eta N) (chaosSampleLaw M).toMeasure,
      (∑' j : ℕ, Paper.prefix_bank_Fmaj (s / 2) n w j g) ≠ ⊤ := by
    rw [Paper.prefix_eta_law M eta hEta N]
    exact Paper.prefix_bank_Fmaj_tsum_ae M (s / 2) half_pos n w
  filter_upwards [ae_of_ae_map (Paper.prefix_eta_aemeasurable M eta hEta N) hpush] with omega h
  exact ne_top_of_le_ne_top h (aux_lfgc_p_trunc_lp_f_ffull_le_bank s hs.le n w (eta N omega))

/-- Product-score truncation remainder under the bilateral law. -/
theorem aux_lfgc_p_trunc_lp_pcand_rem_eLp (hd : 2 ≤ d) [NeZero d] (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (p : ℝ)
    (hp : 1 ≤ p) :
    ∃ C0 delta0 : ℝ, 0 ≤ C0 ∧ 0 < delta0 ∧ ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (eta : ℕ → BilateralField d → PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (N n : ℕ) (w : Vec d) (H : ℕ),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega) ≠ ⊤) ∧
        eLpNorm (fun omega =>
            (Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega)).toReal -
              (Paper.aux_lem_band_piece_product_trunc_Pcand d s n w (eta N omega) H).toReal)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0 * (3 : ℝ) ^ (-(s / 16) * (H : ℝ))) := by
  obtain ⟨C0, delta0, hC0, hdelta0, hcore⟩ := Paper.aux_lem_band_piece_product_trunc_core d hd s hs p hp
  refine ⟨C0, delta0, hC0, hdelta0, fun M hM eta hEta N n w H => ?_⟩
  obtain ⟨hfin, hbound⟩ := hcore M hM n w H
  have hmeasEta := Paper.prefix_eta_aemeasurable M eta hEta N
  have hlaw := Paper.prefix_eta_law M eta hEta N
  refine ⟨?_, ?_⟩
  · have hpush : ∀ᵐ g ∂Measure.map (eta N) (chaosSampleLaw M).toMeasure,
        Paper.aux_lem_band_piece_product_Praw d s n w g ≠ ⊤ := by rw [hlaw]; exact hfin
    exact ae_of_ae_map hmeasEta hpush
  · have hgmeas : Measurable (fun g : PotentialSample d =>
        (Paper.aux_lem_band_piece_product_Praw d s n w g).toReal -
          (Paper.aux_lem_band_piece_product_trunc_Pcand d s n w g H).toReal) :=
      (ENNReal.measurable_toReal.comp (Paper.aux_lem_prefix_limit_actual_Psc_meas s n w)).sub
        (ENNReal.measurable_toReal.comp (Paper.aux_lem_band_piece_product_trunc_Pcand_meas d s n H w))
    have hmap : eLpNorm (fun g : PotentialSample d =>
        (Paper.aux_lem_band_piece_product_Praw d s n w g).toReal -
          (Paper.aux_lem_band_piece_product_trunc_Pcand d s n w g H).toReal)
        (ENNReal.ofReal p) M.P.toMeasure =
        eLpNorm (fun omega : BilateralField d =>
            (Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega)).toReal -
              (Paper.aux_lem_band_piece_product_trunc_Pcand d s n w (eta N omega) H).toReal)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure := by
      rw [← hlaw]
      exact eLpNorm_map_measure hgmeas.aestronglyMeasurable hmeasEta
    rw [← hmap]
    exact hbound

/-- Bad-score truncation remainder. -/
theorem lfgc_p_trunc_lp [NeZero d] (hd1 : (1 : ℝ) ≤ (d : ℝ)) (M : GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (heps : 0 < eps)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N n : ℕ) (w : Vec d) (H : ℕ) (p : ℝ) (hp : 1 ≤ p) {BF BP : ℝ≥0∞}
    (hPfin : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega) ≠ ⊤)
    (hF : eLpNorm (fun omega => (aux_lfgc_p_trunc_ffull s n w (eta N omega)).toReal -
      (aux_lfgc_p_trunc_ftr s n w H (eta N omega)).toReal) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ BF)
    (hP : eLpNorm (fun omega =>
      (Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega)).toReal -
        (Paper.aux_lem_band_piece_product_trunc_Pcand d s n w (eta N omega) H).toReal)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ BP) :
    eLpNorm (fun omega => aux_lfgc_p_trunc_zfull M s eps n w (eta N omega) - aux_lfgc_p_trunc_ztr M s eps n w H (eta N omega))
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (eps / 2)⁻¹ * BF + ENNReal.ofReal 6⁻¹ * BP := by
  set μ := (chaosSampleLaw M).toMeasure
  have hmeasEta := Paper.prefix_eta_aemeasurable M eta hEta N
  have h1 : eps / 2 < eps := by linarith
  have hFfin := aux_lfgc_p_trunc_lp_ffull_ae_finite M s hs eta hEta N n w
  have hFtfin : ∀ᵐ omega ∂μ, aux_lfgc_p_trunc_ftr s n w H (eta N omega) ≠ ⊤ := by
    filter_upwards [hFfin] with omega h
    exact ne_top_of_le_ne_top h (aux_lfgc_p_trunc_lp_f_ftr_le_ffull s n w H (eta N omega))
  have hPcfin : ∀ᵐ omega ∂μ,
      Paper.aux_lem_band_piece_product_trunc_Pcand d s n w (eta N omega) H ≠ ⊤ :=
    Eventually.of_forall fun omega =>
      Paper.aux_lem_band_piece_product_trunc_Pcand_ne_top d hd1 s n H w (eta N omega)
  have hrF := Paper.aux_lem_band_piece_product_eramp_eLpNorm_le (μ := μ) (ENNReal.ofReal p)
    (eps / 2) eps (by linarith) h1 (fun omega => aux_lfgc_p_trunc_ffull s n w (eta N omega))
    (fun omega => aux_lfgc_p_trunc_ftr s n w H (eta N omega)) hFfin hFtfin
  have hrP := Paper.aux_lem_band_piece_product_eramp_eLpNorm_le (μ := μ) (ENNReal.ofReal p)
    6 12 (by norm_num) (by norm_num)
    (fun omega => Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega))
    (fun omega => Paper.aux_lem_band_piece_product_trunc_Pcand d s n w (eta N omega) H)
    hPfin hPcfin
  have hsplit : (fun omega => aux_lfgc_p_trunc_zfull M s eps n w (eta N omega) - aux_lfgc_p_trunc_ztr M s eps n w H (eta N omega)) =
      (fun omega => aux_lfgc_p_trunc_eramp (eps / 2) eps (aux_lfgc_p_trunc_ffull s n w (eta N omega)) -
          aux_lfgc_p_trunc_eramp (eps / 2) eps (aux_lfgc_p_trunc_ftr s n w H (eta N omega))) +
        (fun omega => aux_lfgc_p_trunc_eramp 6 12 (Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega)) -
          aux_lfgc_p_trunc_eramp 6 12 (Paper.aux_lem_band_piece_product_trunc_Pcand d s n w (eta N omega) H)) := by
    funext omega
    simp only [aux_lfgc_p_trunc_zfull, aux_lfgc_p_trunc_ztr, Pi.add_apply]
    ring
  have hmF : AEStronglyMeasurable (fun omega => aux_lfgc_p_trunc_eramp (eps / 2) eps (aux_lfgc_p_trunc_ffull s n w (eta N omega)) -
      aux_lfgc_p_trunc_eramp (eps / 2) eps (aux_lfgc_p_trunc_ftr s n w H (eta N omega))) μ := by
    have hff : Measurable (fun g : PotentialSample d => aux_lfgc_p_trunc_eramp (eps / 2) eps (aux_lfgc_p_trunc_ffull s n w g) -
        aux_lfgc_p_trunc_eramp (eps / 2) eps (aux_lfgc_p_trunc_ftr s n w H g)) := by
      refine ((aux_lfgc_p_trunc_measurable_eramp _ _ h1).comp ?_).sub ((aux_lfgc_p_trunc_measurable_eramp _ _ h1).comp
        (aux_lfgc_p_trunc_measurable_ftr s n w H))
      have h := Paper.aux_lem_prefix_limit_actual_Fsc_meas (d := d) s n w
      simpa only [aux_lfgc_p_trunc_ffull, aux_lem_band_piece_field_term, aux_lem_band_piece_field_normOn] using! h
    exact (hff.comp_aemeasurable hmeasEta).aestronglyMeasurable
  have hmP : AEStronglyMeasurable (fun omega =>
      aux_lfgc_p_trunc_eramp 6 12 (Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega)) -
        aux_lfgc_p_trunc_eramp 6 12 (Paper.aux_lem_band_piece_product_trunc_Pcand d s n w (eta N omega) H)) μ := by
    have hff : Measurable (fun g : PotentialSample d =>
        aux_lfgc_p_trunc_eramp 6 12 (Paper.aux_lem_band_piece_product_Praw d s n w g) -
          aux_lfgc_p_trunc_eramp 6 12 (Paper.aux_lem_band_piece_product_trunc_Pcand d s n w g H)) :=
      ((aux_lfgc_p_trunc_measurable_eramp 6 12 (by norm_num)).comp
        (Paper.aux_lem_prefix_limit_actual_Psc_meas s n w)).sub
        ((aux_lfgc_p_trunc_measurable_eramp 6 12 (by norm_num)).comp
          (Paper.aux_lem_band_piece_product_trunc_Pcand_meas d s n H w))
    exact (hff.comp_aemeasurable hmeasEta).aestronglyMeasurable
  have h1p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  rw [hsplit]
  refine (eLpNorm_add_le h1p).trans (add_le_add ?_ ?_)
  · have hmFraw : AEStronglyMeasurable (fun omega =>
        (min 1 ((aux_lfgc_p_trunc_ffull s n w (eta N omega) - ENNReal.ofReal (eps / 2)) /
          ENNReal.ofReal (eps - eps / 2))).toReal -
        (min 1 ((aux_lfgc_p_trunc_ftr s n w H (eta N omega) - ENNReal.ofReal (eps / 2)) /
          ENNReal.ofReal (eps - eps / 2))).toReal) μ := by
      simpa only [aux_lfgc_p_trunc_eramp] using! hmF
    rw [RawLp.eLpNorm_eq_guarded hmFraw] at hrF
    have hFraw := (RawLp.eLpNorm_le_guarded _ _ _).trans hF
    have hbound := hrF.trans (mul_le_mul_right hFraw _)
    simpa only [aux_lfgc_p_trunc_eramp, show eps - eps / 2 = eps / 2 by ring] using! hbound
  · have hmPraw : AEStronglyMeasurable (fun omega =>
        (min 1 ((Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega) - ENNReal.ofReal 6) /
          ENNReal.ofReal (12 - 6))).toReal -
        (min 1 ((Paper.aux_lem_band_piece_product_trunc_Pcand d s n w (eta N omega) H - ENNReal.ofReal 6) /
          ENNReal.ofReal (12 - 6))).toReal) μ := by
      simpa only [aux_lfgc_p_trunc_eramp] using! hmP
    rw [RawLp.eLpNorm_eq_guarded hmPraw] at hrP
    have hPraw := (RawLp.eLpNorm_le_guarded _ _ _).trans hP
    have hbound := hrP.trans (mul_le_mul_right hPraw _)
    simpa only [aux_lfgc_p_trunc_eramp, show (12 : ℝ) - 6 = 6 by norm_num] using! hbound

/-- Drift-score truncation remainder. -/
theorem aux_lfgc_p_trunc_lp_dtr_rem_eLp [NeZero d] (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N n : ℕ) (w : Vec d) (L : ℕ) (q : ℝ) (hq : 1 ≤ q) (P : ℝ) (hP0 : 0 ≤ P)
    (hPb : ∀ j : ℕ, eLpNorm (fun omega : BilateralField d =>
      Paper.aux_prefix_bank_maxObs j j w (eta N omega)) (ENNReal.ofReal q)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal P)
    (hDfin : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, aux_lfgc_p_trunc_dfull M s n w (eta N omega) ≠ ⊤) :
    eLpNorm (fun omega => (aux_lfgc_p_trunc_dfull M s n w (eta N omega)).toReal -
        (aux_lfgc_p_trunc_dtr M s n w L (eta N omega)).toReal)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (P * (3 / 2) * ((3 : ℝ) ^ (L + 1))⁻¹) := by
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (lfgc_p_trunc_lp_d M eta hEta N n w L q hq P hP0 hPb)
  filter_upwards [hDfin] with omega hfin
  rw [aux_lfgc_p_trunc_lp_d_dfull_eq_dtr_add M s n w L] at hfin ⊢
  obtain ⟨h1, h2⟩ := ENNReal.add_ne_top.mp hfin
  rw [ENNReal.toReal_add h1 h2]
  ring

end Paper
