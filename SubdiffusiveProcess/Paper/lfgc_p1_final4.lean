module

public import SubdiffusiveProcess.Paper.lfgc_p1_final3

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Interval witnesses for the failure of the prefix conjunct. -/
theorem lfgc_p1_final4 (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sobolev : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (lam : ℝ) (hlam : 0 < lam)
    (en nc ns : ℕ) (enDepth : Fin en → ℕ) (hdepth : ∀ e, enDepth e ≤ 3) (buffer k0 : ℕ)
    (hk0 : 1 ≤ k0) {R : ℝ} (hR : 0 < R) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (eta : ℕ → BilateralField d → PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          _root_.SubdiffusiveProcess.Paper.primitive_scores d M sigma eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
      ∀ Carrier : Set (BilateralField d),
        (∀ omega ∈ Carrier, ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
          omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        (∀ omega ∈ Carrier, ∀ N, _root_.SubdiffusiveProcess.Paper.primitive_scores d M sigma eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => Praw N m y omega)
          (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        (∀ omega ∈ Carrier, ∀ (N n : ℕ) (y : Vec d), Draw N n y omega ≠ ⊤) →
      ∀ (m k : ℕ) (z : Vec d) (cmpShift : Fin nc → Vec d) (shift : Fin ns → Vec d),
        IsTailCover (chaosSampleLaw M).toMeasure (aux_lfgc_family_cover_nodeWin d k)
          (Carrier ∩ {omega | ¬ aux_lfgc_rhs_bridge_rhsP1OK en nc ns enDepth cmpShift shift buffer k0 lam Draw Z m k z omega})
          (fun h => ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 2)) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hs0 := hsigma.1
  have heps0 := heps.1
  obtain ⟨aZ, cZ, wZ, haZ, hcZ, hwZ, hbZ⟩ := lfgc_sum_band hd I Poincare Extension MeyersMorrey
    Sobolev D Dbase Cresp hCresp sigma hsigma eps heps false
  obtain ⟨aD, cD, wD, haD, hcD, hwD, hbD⟩ := lfgc_sum_band hd I Poincare Extension MeyersMorrey
    Sobolev D Dbase Cresp hCresp sigma hsigma eps heps true
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = min (min aZ aD) 1 := ⟨_, rfl⟩
  have ha'0 : 0 < a' := by rw [ha']; exact lt_min (lt_min haZ haD) one_pos
  have ha'1 : a' ≤ 1 := by rw [ha']; exact min_le_right _ _
  have ha'Z : a' ≤ aZ := by rw [ha']; exact (min_le_left _ _).trans (min_le_left _ _)
  have ha'D : a' ≤ aD := by rw [ha']; exact (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨cL, hcLdef⟩ : ∃ cL : ℕ, cL = ⌈16 / sigma⌉₊ := ⟨_, rfl⟩
  have hcL : 1 ≤ sigma * cL / 16 := by
    have h := Nat.le_ceil (16 / sigma)
    rw [← hcLdef, div_le_iff₀ hs0] at h
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hcL1 : 1 ≤ cL := by
    have : (1 : ℝ) ≤ cL := by nlinarith [hsigma.2]
    exact_mod_cast this
  have hv0 : 0 ≤ (d : ℝ) * Real.log 3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num); positivity
  have hCg0 : 0 ≤ 2 * ((en * ns : ℕ) : ℝ) * ((en * ns + nc + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨p, hp1, hρ, hps⟩ := p1_moment_order (wZ + wD + cL + 1) hR ha'0 hs0 hv0
  have hp0 : 0 < p := by linarith
  have hρ' : ((3 : ℝ) ^ (-a') / (3 : ℝ) ^ (-(a' / 2))) ^ p ≤
      Real.exp (-(2 + (d : ℝ) * Real.log 3 + R * ((wZ + wD + cL + 1 : ℕ) : ℝ))) := by
    rw [aux_lfgc_p1_cover_rpow_div_half]; exact hρ
  obtain ⟨δZ, CpZ, hδZ, hCpZ, hZ⟩ := hbZ p hp1
  obtain ⟨δD, CpD, hδD, hCpD, hDd⟩ := hbD p hp1
  obtain ⟨C0, δP, hC0, hδP, hPc⟩ := aux_lfgc_p_trunc_lp_pcand_rem_eLp hd sigma hsigma p hp1
  obtain ⟨Pb, hPb0, hPbM⟩ := _root_.SubdiffusiveProcess.Paper.aux_lem_band_T234_bank_eLpNorm_affine (d := d) p hp1
  have hEt0 : 0 ≤ 2 / eps * ((1 + d) * aux_lfgc_p1_te_fieldSeries0 d (sigma / 2) ⌈p⌉₊) + C0 / 6 + 3 / 2 * Pb := by
    have := aux_lfgc_p1_te_fieldSeries0_nonneg (d := d) (sigma / 2) ⌈p⌉₊
    positivity
  obtain ⟨L0, Kn, Merr, κ, M', hMerr0, hMerr, hL0, hKn, hM'0, hM'1, hbS, hbL⟩ :=
    lfgc_p1_final (wZ + wD + cL + 1) buffer k0 hR hp1 ha'0 hs0 hlam hv0 hCg0 hEt0 hps hρ'
  have hA0 : 0 < (d : ℝ) * Real.log 3 + R * ((wZ + wD + cL + 1 : ℕ) : ℝ) + 1 := by positivity
  obtain ⟨δW, hδW, hwit⟩ := _root_.SubdiffusiveProcess.Paper.prefix_physical_witness d sigma eps lam
    ((d : ℝ) * Real.log 3 + R * ((wZ + wD + cL + 1 : ℕ) : ℝ) + 1) M' buffer hsigma heps hlam hA0
    hM'0 hM'1
  have hb2 : 0 < 2 + 2 * (buffer : ℝ) := by positivity
  have hsZpos : 0 < (Merr / (2 + 2 * (buffer : ℝ)) / CpZ) ^ (1 / cZ) :=
    Real.rpow_pos_of_pos (div_pos (div_pos hMerr0 hb2) hCpZ) _
  have hsDpos : 0 < (Merr / (2 + 2 * (buffer : ℝ)) / CpD) ^ (1 / cD) :=
    Real.rpow_pos_of_pos (div_pos (div_pos hMerr0 hb2) hCpD) _
  refine ⟨min (min (min δZ δD) (min δP δW)) (min 1 (min ((Merr / (2 + 2 * (buffer : ℝ)) / CpZ) ^
      (1 / cZ)) ((Merr / (2 + 2 * (buffer : ℝ)) / CpD) ^ (1 / cD)))),
    lt_min (lt_min (lt_min hδZ hδD) (lt_min hδP hδW)) (lt_min one_pos (lt_min hsZpos hsDpos)), ?_⟩
  intro M hM Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim Carrier hC1 hC2 hC3
    m k z cmpShift shift
  have hMZ : M.delta ≤ δZ :=
    hM.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hMD : M.delta ≤ δD :=
    hM.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hMP : M.delta ≤ δP :=
    hM.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMW : M.delta ≤ δW :=
    hM.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hM1 : M.delta ≤ 1 := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMsZ := hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMsD := hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδpos : 0 < M.delta := by
    have h := _root_.SubdiffusiveProcess.Paper.aux_psf_sigma_pos M
    have he : _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M = (1 + (d : ℝ)) * M.delta := rfl
    rw [he] at h
    exact (mul_pos_iff_of_pos_left (by positivity)).mp h
  have hsZ : (2 + 2 * (buffer : ℝ)) * (CpZ * M.delta ^ cZ) ≤ Merr := by
    have h := lfgc_p1_cover hCpZ hcZ hδpos (div_pos hMerr0 hb2) rfl hMsZ
    rw [le_div_iff₀ hb2] at h; linarith
  have hsD : (2 + 2 * (buffer : ℝ)) * (CpD * M.delta ^ cD) ≤ Merr := by
    have h := lfgc_p1_cover hCpD hcD hδpos (div_pos hMerr0 hb2) rfl hMsD
    rw [le_div_iff₀ hb2] at h; linarith
  obtain ⟨Y, Eb, hEb0, hEb, hYwin, hYmeas, hYe⟩ := lfgc_p1_final2 M Draw Z (m + k) p wZ wD hCpZ hCpD
    hsZ hsD (fun j w hj h hh => hZ M hMZ Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim
      (m + k) j w hj h hh)
    (fun j w hj h hh => hDd M hMD Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim
      (m + k) j w hj h hh) ha'Z ha'D hδpos
  have hTe := fun b j w L => lfgc_p1_te hd1 M hM1 sigma eps hsigma heps0 eta hEta F Praw Rraw Draw Z
    rawGood hPrim p hp1 hC0 hPb0 (fun N' n w' H' => hPc M hMP eta hEta N' n w' H')
    (fun N' z' i => aux_lfgc_p1_fin_bank_eq_level_bound hPbM M eta hEta N' z' i) b (m + k) j w L
  obtain ⟨hT, hU, herr, hwin, hlim⟩ := lfgc_p1_final3 M sigma eps hs0 heps0 eta hEta F Praw Rraw Draw Z
    rawGood hPrim Carrier hC1 hC2 hC3 en nc ns enDepth hdepth cmpShift shift buffer k0 hk0 m k z cL L0
    (wZ + wD) hcL1 hcL Y hYwin hYmeas hp1 hEb0 hEt0 hYe hTe hEb hL0 hMerr ha'0 ha'1
  have hq0 : 0 < (3 : ℝ) ^ (-a') := by positivity
  have hq1 : (3 : ℝ) ^ (-a') ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hr0 : 0 < (3 : ℝ) ^ (-(a' / 2)) := by positivity
  have hr1 : (3 : ℝ) ^ (-(a' / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨W, hWm, hWp, hWc⟩ := hwit M hMW eta hEta F Praw Rraw Draw Z rawGood hPrim m k k0 hk0
    (aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z) (fun _ i => enDepth i.1.1) (fun _ i => i.2.1.1)
    (fun _ i => i.2.2) (aux_lfgc_family_cover_nodeWin d k) (fun h => Real.exp (-R * (h : ℝ)) / 2)
    (fun h => by positivity) (aux_lfgc_p1_approx_p1Wfun (wZ + wD + cL + 1) L0 buffer)
    (aux_lfgc_p1_approx_p1Wfun_injective (wZ + wD + cL + 1) L0 buffer (by omega)) Kn hKn p Merr ((3 : ℝ) ^ (-a'))
    ((3 : ℝ) ^ (-(a' / 2))) (lam * (1 - (3 : ℝ) ^ (-(a' / 2))) / 4)
    (2 * ((en * ns : ℕ) : ℝ) * ((en * ns + nc + 1 : ℕ) : ℝ)) ((d : ℝ) * Real.log 3) hp0 hMerr0.le hq0
    hq1 hr0 hr1 rfl hCg0 hv0 (aux_lfgc_p1_index_card_p1Idx_le en nc ns enDepth cmpShift shift k z)
    (fun D i H => aux_lfgc_p1_approx_p1U M sigma eps m k buffer cL L0 (enDepth i.1.1) i.2.1.1 i.2.2 Y D H)
    hT (fun D i H => hU D i H) herr hwin (fun H _ => hbS H) hbL Carrier hlim
  refine ⟨W, hWm, hWp, ?_⟩
  rintro omega ⟨hωC, hω⟩
  exact hWc ⟨hωC, lfgc_p1_index en nc ns enDepth cmpShift shift buffer k0 lam Draw Z m k z omega hω⟩

end SubdiffusiveProcess.Paper
