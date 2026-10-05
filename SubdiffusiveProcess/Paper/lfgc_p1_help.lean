module

public import SubdiffusiveProcess.Paper.lfgc_p1_approx2
public import SubdiffusiveProcess.Lfgc.P1Const
public import SubdiffusiveProcess.Paper.lfgc_p1_num

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Helpers for the prefix cover

Measurability of the literal and truncated summands and of the approximants at every index, a
choice function for band approximants, and the uniform truncation-error bound
`E_t 3^{-σL/16}` for both score tags.
-/

open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p1_help_measurable_zfull [NeZero d] (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps) (n : ℕ)
    (y : Vec d) : Measurable (aux_lfgc_p_trunc_zfull M s eps n y) := by
  have h1 : eps / 2 < eps := by linarith
  have h3 : eps ^ 2 / 4 < eps ^ 2 := by have := pow_pos heps 2; linarith
  have hF : Measurable (aux_lfgc_p_trunc_ffull (d := d) s n y) := by
    have h := _root_.SubdiffusiveProcess.Paper.aux_lem_prefix_limit_actual_Fsc_meas (d := d) s n y
    simpa only [aux_lfgc_p_trunc_ffull, aux_lem_band_piece_field_term, aux_lem_band_piece_field_normOn] using! h
  exact (((aux_lfgc_p_trunc_measurable_eramp _ _ h1).comp hF).add ((aux_lfgc_p_trunc_measurable_eramp 6 12 (by norm_num)).comp
    (_root_.SubdiffusiveProcess.Paper.aux_lem_prefix_limit_actual_Psc_meas s n y))).add
    ((aux_lfgc_p_trunc_measurable_eramp _ _ h3).comp (aux_lfgc_p_trunc_measurable_rfull M s n y))

theorem lfgc_p1_help [NeZero d] (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (b : Bool) (N : ℕ) (j : ℤ) (w : Vec d) :
    AEStronglyMeasurable (aux_lfgc_sum_band_summand b Draw Z N j w) (chaosSampleLaw M).toMeasure := by
  have hmeasEta := _root_.SubdiffusiveProcess.Paper.prefix_eta_aemeasurable M eta hEta N
  set n' := ((N : ℤ) - j).toNat
  cases b
  · refine (((aux_lfgc_p1_help_measurable_zfull M s eps heps n' ((3 : ℝ) ^ N • w)).comp_aemeasurable
      hmeasEta).aestronglyMeasurable).congr ?_
    filter_upwards [hPrim] with omega hp
    simp only [aux_lfgc_sum_band_summand, Bool.false_eq_true, ite_false, Function.comp]
    exact ((aux_lfgc_sum_trunc_scores_formula M s eps (eta N omega) _ _ _ _ _ _ (hp N) n' _).2).symm
  · refine ((ENNReal.measurable_toReal.comp (aux_lfgc_p_trunc_measurable_dfull M s n' ((3 : ℝ) ^ N • w))).comp_aemeasurable
      hmeasEta).aestronglyMeasurable.congr ?_
    filter_upwards [hPrim] with omega hp
    simp only [aux_lfgc_sum_band_summand, ite_true, Function.comp]
    rw [(aux_lfgc_sum_trunc_scores_formula M s eps (eta N omega) _ _ _ _ _ _ (hp N) n' _).1]

theorem aux_lfgc_p1_help_summandTr_measurable [NeZero d] (b : Bool) (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps)
    (N : ℕ) (j : ℤ) (w : Vec d) (L : ℕ) : Measurable (aux_lfgc_sum_trunc_summandTr b M s eps N j w L) := by
  unfold aux_lfgc_sum_trunc_summandTr
  cases b
  · exact (lfgc_p_trunc M s eps heps _ _ L).comp (aux_lfgc_layer_tail_measurable_canonEta N)
  · exact (ENNReal.measurable_toReal.comp (aux_lfgc_p_trunc_measurable_dtr M s _ _ L)).comp (aux_lfgc_layer_tail_measurable_canonEta N)

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- A choice function for a family of existence statements under side conditions. -/
theorem aux_lfgc_p1_help_choose_family {β Ω : Type*} (N : ℤ) (P : ℤ → β → ℕ → (Ω → ℝ) → Prop)
    (h : ∀ j w, j ≤ N → ∀ h : ℕ, 1 ≤ h → ∃ Y, P j w h Y) :
    ∃ Y : ℤ → β → ℕ → Ω → ℝ, (∀ j w hh, j ≤ N → 1 ≤ hh → P j w hh (Y j w hh)) ∧
      (∀ j w hh, ¬ (j ≤ N ∧ 1 ≤ hh) → Y j w hh = 0) := by
  classical
  refine ⟨fun j w hh => if hc : j ≤ N ∧ 1 ≤ hh then Classical.choose (h j w hc.1 hh hc.2) else 0,
    fun j w hh hj hh1 => ?_, fun j w hh hc => ?_⟩
  · have hc : j ≤ N ∧ 1 ≤ hh := ⟨hj, hh1⟩
    simp only [hc, and_self, dite_eq_left]
    exact Classical.choose_spec (h j w hc.1 hh hc.2)
  · simp only [hc, dite_eq_right, not_false_eq_true]

end SubdiffusiveProcess.Paper
