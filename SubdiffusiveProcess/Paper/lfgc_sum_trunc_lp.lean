module

public import SubdiffusiveProcess.Paper.lfgc_sum_trunc

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# `L^p` error of the truncated prefix summands

On a sample family with the canonical formula almost surely and the primitive-score clauses
almost surely, the literal prefix aux_lfgc_sum_band_summand and its truncated version differ in `L^p` by the
field/product remainders (bad score) or the drift-tail remainder (drift score).
-/

open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_sum_trunc_lp_eta_ae_canon (M : GMCModel d) (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) (N : ℕ) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, eta N omega = aux_lfgc_layer_tail_canonEta N omega := by
  filter_upwards [hEta] with omega h
  exact aux_lfgc_layer_tail_canonEta_eq N (eta N) omega (fun i y => h N i y)

theorem aux_lfgc_sum_trunc_lp_dfull_ae_finite [NeZero d] (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) (N n : ℕ) (w : Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, aux_lfgc_p_trunc_dfull M s n w (eta N omega) ≠ ⊤ := by
  have hpush : ∀ᵐ g ∂Measure.map (eta N) (chaosSampleLaw M).toMeasure,
      (∑' j : ℕ, _root_.SubdiffusiveProcess.Paper.aux_psf_Dmaj4 n w j g) ≠ ⊤ := by
    rw [_root_.SubdiffusiveProcess.Paper.prefix_eta_law M eta hEta N]
    exact _root_.SubdiffusiveProcess.Paper.aux_psf_Dmaj4_tsum_ae M n w
  filter_upwards [ae_of_ae_map (_root_.SubdiffusiveProcess.Paper.prefix_eta_aemeasurable M eta hEta N) hpush] with omega h
  exact _root_.SubdiffusiveProcess.Paper.aux_psf_Dsc_ne_top M s hs n w (eta N omega) h

/-- `L^p` error of the truncated bad-score aux_lfgc_sum_band_summand. -/
theorem lfgc_sum_trunc_lp [NeZero d] (hd1 : (1 : ℝ) ≤ (d : ℝ)) (M : GMCModel d) (s eps : ℝ)
    (hs : 0 < s) (heps : 0 < eps) (eta : ℕ → BilateralField d → PotentialSample d)
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
    (N : ℕ) (j : ℤ) (w : Vec d) (L : ℕ) (p : ℝ) (hp : 1 ≤ p) {BF BP : ℝ≥0∞}
    (hPfin : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      _root_.SubdiffusiveProcess.Paper.aux_lem_band_piece_product_Praw d s ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w)
        (eta N omega) ≠ ⊤)
    (hF : eLpNorm (fun omega => (aux_lfgc_p_trunc_ffull s ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) (eta N omega)).toReal -
      (aux_lfgc_p_trunc_ftr s ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) L (eta N omega)).toReal) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤ BF)
    (hP : eLpNorm (fun omega =>
      (_root_.SubdiffusiveProcess.Paper.aux_lem_band_piece_product_Praw d s ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w)
        (eta N omega)).toReal -
      (_root_.SubdiffusiveProcess.Paper.aux_lem_band_piece_product_trunc_Pcand d s ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w)
        (eta N omega) L).toReal) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ BP) :
    eLpNorm (fun omega => aux_lfgc_sum_band_summand false Draw Z N j w omega - aux_lfgc_sum_trunc_summandTr false M s eps N j w L omega)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (eps / 2)⁻¹ * BF + ENNReal.ofReal 6⁻¹ * BP := by
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
    (lfgc_p_trunc_lp hd1 M s eps hs heps eta hEta N ((N : ℤ) - j).toNat _ L p hp hPfin hF hP)
  filter_upwards [hPrim, aux_lfgc_sum_trunc_lp_eta_ae_canon M eta hEta N] with omega hp' hc
  have hZ := (aux_lfgc_sum_trunc_scores_formula M s eps (eta N omega) _ _ _ _ _ _ (hp' N)
    ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w)).2
  simp only [aux_lfgc_sum_band_summand, aux_lfgc_sum_trunc_summandTr, Bool.false_eq_true, ite_false]
  rw [hZ, hc]

/-- `L^p` error of the truncated drift aux_lfgc_sum_band_summand. -/
theorem aux_lfgc_sum_trunc_lp_summandTr_true_eLp [NeZero d] (M : GMCModel d) (s eps : ℝ) (hs : 0 < s)
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
    (N : ℕ) (j : ℤ) (w : Vec d) (L : ℕ) (q : ℝ) (hq : 1 ≤ q) (P : ℝ) (hP0 : 0 ≤ P)
    (hPb : ∀ i : ℕ, eLpNorm (fun omega : BilateralField d =>
      _root_.SubdiffusiveProcess.Paper.aux_prefix_bank_maxObs i i ((3 : ℝ) ^ N • w) (eta N omega)) (ENNReal.ofReal q)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal P) :
    eLpNorm (fun omega => aux_lfgc_sum_band_summand true Draw Z N j w omega - aux_lfgc_sum_trunc_summandTr true M s eps N j w L omega)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (P * (3 / 2) * ((3 : ℝ) ^ (L + 1))⁻¹) := by
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
    (aux_lfgc_p_trunc_lp_dtr_rem_eLp M s hs eta hEta N ((N : ℤ) - j).toNat _ L q hq P hP0 hPb
      (aux_lfgc_sum_trunc_lp_dfull_ae_finite M s hs eta hEta N ((N : ℤ) - j).toNat _))
  filter_upwards [hPrim, aux_lfgc_sum_trunc_lp_eta_ae_canon M eta hEta N] with omega hp' hc
  have hD := (aux_lfgc_sum_trunc_scores_formula M s eps (eta N omega) _ _ _ _ _ _ (hp' N)
    ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w)).1
  simp only [aux_lfgc_sum_band_summand, aux_lfgc_sum_trunc_summandTr, ite_true]
  rw [hD, hc]

end SubdiffusiveProcess.Paper
