module

public import SubdiffusiveProcess.Paper.lfgc_p_trunc_lp_f

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `L^q` remainder of the truncated drift score

The gradient terms of the drift score beyond layer `n + L` are dominated by the layer banks
`3^{n-j} B_j`; with the uniform `L^q` bank bound `P` of lem_band this gives
`‖aux_lfgc_p_trunc_dfull − aux_lfgc_p_trunc_dtr L‖_q ≤ (3/2) P 3^{-(L+1)}`, uniformly in the cutoff, the level and the centre.
-/

open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p_trunc_lp_d_dfull_eq_dtr_add (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) (L : ℕ)
    (g : PotentialSample d) :
    aux_lfgc_p_trunc_dfull M s n y g = aux_lfgc_p_trunc_dtr M s n y L g + ∑' j, (if n + L < j then aux_lfgc_p_trunc_dtail n y g j else 0) := by
  unfold aux_lfgc_p_trunc_dfull aux_lfgc_p_trunc_dtr
  rw [add_assoc, ← _root_.SubdiffusiveProcess.Paper.aux_lem_band_D_tsum_split (fun j => aux_lfgc_p_trunc_dtail n y g j) (n + L)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p_trunc_lp_d_dtail_le_bankmaj (n : ℕ) (y : Vec d) (g : PotentialSample d) (j : ℕ) :
    aux_lfgc_p_trunc_dtail n y g j ≤ _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j g := by
  unfold aux_lfgc_p_trunc_dtail
  by_cases hnj : n ≤ j
  · rw [ite_eq_left hnj]
    exact _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_termFn_le_bankmaj n y j g hnj
  · rw [ite_eq_right hnj]; exact bot_le

/-- Uniform `L^q` remainder of the truncated drift gradient series. -/
theorem lfgc_p_trunc_lp_d (M : GMCModel d) (eta : ℕ → BilateralField d → PotentialSample d)
    (heta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N n : ℕ) (y : Vec d) (L : ℕ) (q : ℝ) (hq : 1 ≤ q) (P : ℝ) (hP0 : 0 ≤ P)
    (hPb : ∀ j : ℕ, eLpNorm (fun omega : BilateralField d =>
      _root_.SubdiffusiveProcess.Paper.aux_prefix_bank_maxObs j j y (eta N omega)) (ENNReal.ofReal q)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal P) :
    eLpNorm (fun omega =>
        (∑' j, (if n + L < j then aux_lfgc_p_trunc_dtail n y (eta N omega) j else 0)).toReal)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (P * (3 / 2) * ((3 : ℝ) ^ (L + 1))⁻¹) := by
  set μ := (chaosSampleLaw M).toMeasure
  set a := n + L with ha
  have hmeasEta := _root_.SubdiffusiveProcess.Paper.prefix_eta_aemeasurable M eta heta N
  have hlift : ∀ᵐ omega ∂μ, (∑' j : ℕ, _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j (eta N omega)) ≠ ⊤ := by
    have hpush : ∀ᵐ g ∂Measure.map (eta N) μ,
        (∑' j : ℕ, _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j g) ≠ ⊤ := by
      rw [_root_.SubdiffusiveProcess.Paper.prefix_eta_law M eta heta N]
      exact _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj_tsum_ae M n y
    exact ae_of_ae_map hmeasEta hpush
  set g' : ℕ → BilateralField d → ℝ := fun j omega =>
    (if a < j then _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j (eta N omega) else 0).toReal with hg'
  have hbank_ne : ∀ j omega, _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j omega ≠ ⊤ := by
    intro j omega
    unfold _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj
    split_ifs
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  have hstep0 : ∀ᵐ omega ∂μ,
      ‖(∑' j, (if a < j then aux_lfgc_p_trunc_dtail n y (eta N omega) j else 0)).toReal‖ ≤
        ‖∑' j, g' j omega‖ := by
    filter_upwards [hlift] with omega hom
    have hle : (∑' j, (if a < j then aux_lfgc_p_trunc_dtail n y (eta N omega) j else 0)) ≤
        ∑' j, (if a < j then _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j (eta N omega) else 0) :=
      ENNReal.tsum_le_tsum fun j => by
        split_ifs
        · exact aux_lfgc_p_trunc_lp_d_dtail_le_bankmaj n y (eta N omega) j
        · exact le_rfl
    have hne : (∑' j, (if a < j then _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j (eta N omega)
        else 0)) ≠ ⊤ :=
      ne_top_of_le_ne_top hom (ENNReal.tsum_le_tsum fun j => by split_ifs <;> simp)
    have heq : (∑' j, (if a < j then _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j (eta N omega)
        else 0)).toReal = ∑' j, g' j omega := by
      rw [hg', ENNReal.tsum_toReal_eq]
      intro j; split_ifs
      · exact hbank_ne j _
      · exact ENNReal.zero_ne_top
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ← heq,
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hne hle
  have htailMeas : AEStronglyMeasurable (fun omega =>
      (∑' j, (if a < j then aux_lfgc_p_trunc_dtail n y (eta N omega) j else 0)).toReal) μ := by
    apply AEMeasurable.aestronglyMeasurable
    apply ENNReal.measurable_toReal.comp_aemeasurable
    apply AEMeasurable.tsum
    intro j
    by_cases haj : a < j
    · simp only [haj, ite_true]
      exact (aux_lfgc_p_trunc_measurable_dtail n y j).comp_aemeasurable hmeasEta
    · simp only [haj, ite_false]
      exact aemeasurable_const
  refine (eLpNorm_mono_ae htailMeas hstep0).trans ?_
  have hg'meas : ∀ j, AEStronglyMeasurable (g' j) μ := by
    intro j
    have hae : AEMeasurable (fun omega => if a < j then
        _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j (eta N omega) else 0) μ := by
      by_cases haj : a < j
      · simp only [haj, ite_true]
        exact (_root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj_measurable n y j).comp_aemeasurable hmeasEta
      · simp only [haj, ite_false]; exact aemeasurable_const
    exact (ENNReal.measurable_toReal.comp_aemeasurable hae).aestronglyMeasurable
  have hg'point : ∀ j omega, a < j → g' j omega =
      (3 : ℝ) ^ n / (3 : ℝ) ^ j * _root_.SubdiffusiveProcess.Paper.aux_prefix_bank_maxObs j j y (eta N omega) := by
    intro j omega haj
    have hnj : n ≤ j := by omega
    rw [hg']
    simp only [haj, ite_true]
    unfold _root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj
    simp only [hnj, ite_true]
    exact ENNReal.toReal_ofReal (mul_nonneg (by positivity)
      (_root_.SubdiffusiveProcess.Paper.prefix_bank_maxObs_nonneg j j y (eta N omega)))
  have hterm_le : ∀ j, eLpNorm (g' j) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (if a < j then (3 : ℝ) ^ n / (3 : ℝ) ^ j * P else 0) := by
    intro j
    by_cases haj : a < j
    · have hae : eLpNorm (g' j) (ENNReal.ofReal q) μ =
          eLpNorm (fun omega => (3 : ℝ) ^ n / (3 : ℝ) ^ j *
            _root_.SubdiffusiveProcess.Paper.aux_prefix_bank_maxObs j j y (eta N omega)) (ENNReal.ofReal q) μ :=
        eLpNorm_congr_ae (Eventually.of_forall fun omega => hg'point j omega haj)
      have hscale := _root_.SubdiffusiveProcess.Paper.aux_lem_band_piece_field_scale ((3 : ℝ) ^ n / (3 : ℝ) ^ j)
        (by positivity) (fun omega => _root_.SubdiffusiveProcess.Paper.aux_prefix_bank_maxObs j j y (eta N omega))
        (ENNReal.ofReal q) P (hPb j)
      rw [hae]
      simpa [haj] using hscale
    · have hz : g' j = fun _ => (0 : ℝ) := by
        funext omega; rw [hg']; simp [haj]
      rw [hz]; simp [haj]
  have hgeom : ∀ m : ℕ, (3 : ℝ) ^ n *
      ∑ j ∈ (Finset.range m).filter (fun j => a < j), ((1 : ℝ) / 3) ^ j ≤
      (3 / 2) * ((3 : ℝ) ^ (L + 1))⁻¹ := by
    intro m
    have hg := _root_.SubdiffusiveProcess.Paper.aux_lem_band_D_geom_tail_sum ((1 : ℝ) / 3) (by norm_num) (by norm_num) a m
    have hk0 : (0 : ℝ) ≤ (3 : ℝ) ^ n := by positivity
    refine (mul_le_mul_of_nonneg_left hg hk0).trans (le_of_eq ?_)
    have haeq : a + 1 = n + (L + 1) := by rw [ha]; ring
    rw [haeq, div_eq_mul_inv, one_div, inv_pow, pow_add]
    field_simp
    ring
  have hsum_le : ∀ m, ∑ j ∈ Finset.range m, eLpNorm (g' j) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (P * (3 / 2) * ((3 : ℝ) ^ (L + 1))⁻¹) := by
    intro m
    calc ∑ j ∈ Finset.range m, eLpNorm (g' j) (ENNReal.ofReal q) μ
        ≤ ∑ j ∈ Finset.range m, ENNReal.ofReal
            (if a < j then (3 : ℝ) ^ n / (3 : ℝ) ^ j * P else 0) :=
          Finset.sum_le_sum fun j _ => hterm_le j
      _ = ENNReal.ofReal (∑ j ∈ Finset.range m,
            (if a < j then (3 : ℝ) ^ n / (3 : ℝ) ^ j * P else 0)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro j _
          by_cases haj : a < j <;> simp [haj]; positivity
      _ ≤ ENNReal.ofReal (P * (3 / 2) * ((3 : ℝ) ^ (L + 1))⁻¹) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hrw : ∀ j, (if a < j then (3 : ℝ) ^ n / (3 : ℝ) ^ j * P else 0) =
              P * (if a < j then (3 : ℝ) ^ n * ((1 : ℝ) / 3) ^ j else 0) := by
            intro j
            by_cases haj : a < j
            · simp only [haj, ite_true]; rw [div_pow]; ring_nf
            · simp [haj]
          simp_rw [hrw]
          rw [← Finset.mul_sum]
          have hfilt : ∑ j ∈ Finset.range m,
              (if a < j then (3 : ℝ) ^ n * ((1 : ℝ) / 3) ^ j else 0) =
              (3 : ℝ) ^ n * ∑ j ∈ (Finset.range m).filter (fun j => a < j), ((1 : ℝ) / 3) ^ j := by
            rw [Finset.mul_sum, Finset.sum_filter]
          rw [hfilt]
          calc P * ((3 : ℝ) ^ n *
              ∑ j ∈ (Finset.range m).filter (fun j => a < j), ((1 : ℝ) / 3) ^ j)
              ≤ P * ((3 / 2) * ((3 : ℝ) ^ (L + 1))⁻¹) := mul_le_mul_of_nonneg_left (hgeom m) hP0
            _ = P * (3 / 2) * ((3 : ℝ) ^ (L + 1))⁻¹ := by ring
  have hpsum : ∀ m, eLpNorm (fun omega => ∑ j ∈ Finset.range m, g' j omega)
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (P * (3 / 2) * ((3 : ℝ) ^ (L + 1))⁻¹) := by
    intro m
    have h1q : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
    have hst := (eLpNorm_sum_le (f := g') (s := Finset.range m) (μ := μ) h1q).trans
      (hsum_le m)
    have heqfun : (∑ j ∈ Finset.range m, g' j) =
        (fun omega => ∑ j ∈ Finset.range m, g' j omega) := by
      funext omega; rw [Finset.sum_apply]
    rwa [heqfun] at hst
  have hsummable : ∀ᵐ omega ∂μ, Summable (fun j => g' j omega) := by
    filter_upwards [hlift] with omega hom
    have hs' : Summable (fun j => (_root_.SubdiffusiveProcess.Paper.aux_lem_band_DT4_bankmaj n y j (eta N omega)).toReal) :=
      ENNReal.summable_toReal hom
    refine Summable.of_nonneg_of_le (fun j => ENNReal.toReal_nonneg) (fun j => ?_) hs'
    rw [hg']
    by_cases haj : a < j
    · simp only [haj, ite_true]; exact le_rfl
    · simp only [haj, ite_false]; exact ENNReal.toReal_nonneg
  exact _root_.SubdiffusiveProcess.Paper.prefix_eLpNorm_tsum_le μ g' (ENNReal.ofReal q) _ hg'meas hsummable hpsum

end SubdiffusiveProcess.Paper
