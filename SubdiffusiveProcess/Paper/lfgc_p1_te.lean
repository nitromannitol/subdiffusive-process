module

public import SubdiffusiveProcess.Paper.lfgc_p1_fin

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# The uniform truncation error of the prefix summands

For disorder at most one, both score tags of a prefix aux_lfgc_sum_band_summand differ from their truncations at
depth `L` in `L^p` by at most `E_t 3^{-σL/16}` with
`E_t = (2/ε)(1+d) T₀ + C₀/6 + (3/2) P`, where `T₀` is the unit-scale field series, `C₀` the
product-truncation constant and `P` the equal-level bank bound.
-/

open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The unit-scale field series. -/
noncomputable def aux_lfgc_p1_te_fieldSeries0 (d : ℕ) (s : ℝ) (qn : ℕ) : ℝ :=
  ∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
    (2 * ((qn : ℝ) + 1 + _root_.SubdiffusiveProcess.Paper.prefix_log_card d j))

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p1_te_fieldSeries0_nonneg (s : ℝ) (qn : ℕ) : 0 ≤ aux_lfgc_p1_te_fieldSeries0 d s qn :=
  tsum_nonneg fun j => by
    have := _root_.SubdiffusiveProcess.Paper.prefix_log_card_nonneg d j
    positivity

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p1_te_series_le_fieldSeries0 (M : GMCModel d) (hM : M.delta ≤ 1) (s : ℝ) (qn : ℕ) :
    ∑' j : ℕ, _root_.SubdiffusiveProcess.Paper.prefix_even_series_bound M s qn j ≤ (1 + d) * aux_lfgc_p1_te_fieldSeries0 d s qn := by
  have heq : (fun j : ℕ => _root_.SubdiffusiveProcess.Paper.prefix_even_series_bound M s qn j) =
      fun j : ℕ => _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M * ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
        (2 * ((qn : ℝ) + 1 + _root_.SubdiffusiveProcess.Paper.prefix_log_card d j))) := by
    funext j; unfold _root_.SubdiffusiveProcess.Paper.prefix_even_series_bound; ring
  rw [heq, tsum_mul_left]
  have hσ : _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M ≤ 1 + d := by
    have : _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M = (1 + (d : ℝ)) * M.delta := rfl
    rw [this]; nlinarith
  exact mul_le_mul_of_nonneg_right hσ (aux_lfgc_p1_te_fieldSeries0_nonneg s qn)

/-- The uniform truncation error of both score tags. -/
theorem lfgc_p1_te [NeZero d] (hd1 : (1 : ℝ) ≤ (d : ℝ)) (M : GMCModel d) (hM1 : M.delta ≤ 1)
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : 0 < eps)
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
    (p : ℝ) (hp : 1 ≤ p) {C0 Pb : ℝ} (hC0 : 0 ≤ C0) (hPb0 : 0 ≤ Pb)
    (hPc : ∀ (N n : ℕ) (w : Vec d) (H : ℕ),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        _root_.SubdiffusiveProcess.Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega) ≠ ⊤) ∧
      eLpNorm (fun omega =>
          (_root_.SubdiffusiveProcess.Paper.aux_lem_band_piece_product_Praw d s n w (eta N omega)).toReal -
            (_root_.SubdiffusiveProcess.Paper.aux_lem_band_piece_product_trunc_Pcand d s n w (eta N omega) H).toReal)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C0 * (3 : ℝ) ^ (-(s / 16) * (H : ℝ))))
    (hPbnd : ∀ (N : ℕ) (z : Vec d) (i : ℕ),
      eLpNorm (fun omega : BilateralField d => _root_.SubdiffusiveProcess.Paper.aux_prefix_bank_maxObs i i z (eta N omega))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Pb)
    (b : Bool) (N : ℕ) (j : ℤ) (w : Vec d) (L : ℕ) :
    eLpNorm (fun omega => aux_lfgc_sum_band_summand b Draw Z N j w omega - aux_lfgc_sum_trunc_summandTr b M s eps N j w L omega)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2 / eps * ((1 + d) * aux_lfgc_p1_te_fieldSeries0 d (s / 2) ⌈p⌉₊) + C0 / 6 + 3 / 2 * Pb) *
        (3 : ℝ) ^ (-(s / 16 * (L : ℝ)))) := by
  have hT0 := aux_lfgc_p1_te_fieldSeries0_nonneg (d := d) (s / 2) ⌈p⌉₊
  set T0 := aux_lfgc_p1_te_fieldSeries0 d (s / 2) ⌈p⌉₊
  have hx0 : 0 ≤ (3 : ℝ) ^ (-(s / 16 * (L : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  cases b
  · have hF := lfgc_p_trunc_lp_f M s hs.1 eta hEta N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) L p hp
    obtain ⟨hPfin, hPb⟩ := hPc N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) L
    have h := lfgc_sum_trunc_lp hd1 M s eps hs.1 heps eta hEta F Praw Rraw Draw Z rawGood hPrim N j
      w L p hp hPfin hF hPb
    refine h.trans ?_
    have hser := aux_lfgc_p1_te_series_le_fieldSeries0 M hM1 (s / 2) ⌈p⌉₊
    have hser0 : 0 ≤ ∑' jj : ℕ, _root_.SubdiffusiveProcess.Paper.prefix_even_series_bound M (s / 2) ⌈p⌉₊ jj :=
      tsum_nonneg fun jj => _root_.SubdiffusiveProcess.Paper.prefix_even_series_bound_nonneg M (s / 2) ⌈p⌉₊ jj
    have he : (3 : ℝ) ^ (-(s * (L : ℝ) / 16)) = (3 : ℝ) ^ (-(s / 16 * (L : ℝ))) := by ring_nf
    have he2 : (3 : ℝ) ^ (-(s / 16) * (L : ℝ)) = (3 : ℝ) ^ (-(s / 16 * (L : ℝ))) := by ring_nf
    rw [he, he2, ← ENNReal.ofReal_mul hx0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hepsinv : (eps / 2)⁻¹ = 2 / eps := by field_simp
    rw [hepsinv]
    have h1 : 2 / eps * ((3 : ℝ) ^ (-(s / 16 * (L : ℝ))) *
        ∑' jj : ℕ, _root_.SubdiffusiveProcess.Paper.prefix_even_series_bound M (s / 2) ⌈p⌉₊ jj) ≤
        2 / eps * ((1 + d) * T0) * (3 : ℝ) ^ (-(s / 16 * (L : ℝ))) := by
      have h2e : 0 ≤ 2 / eps := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hser (mul_nonneg h2e hx0)]
    nlinarith [mul_nonneg hPb0 hx0]
  · have h := aux_lfgc_sum_trunc_lp_summandTr_true_eLp M s eps hs.1 eta hEta F Praw Rraw Draw Z rawGood hPrim N j w L p hp
      Pb hPb0 (hPbnd N ((3 : ℝ) ^ N • w))
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hinv : ((3 : ℝ) ^ (L + 1))⁻¹ ≤ (3 : ℝ) ^ (-(s / 16 * (L : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      push_cast
      nlinarith [hs.1, hs.2]
    have hA : 0 ≤ 2 / eps * ((1 + d) * T0) + C0 / 6 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ Pb * (3 / 2)),
      mul_nonneg hA hx0]

end SubdiffusiveProcess.Paper
