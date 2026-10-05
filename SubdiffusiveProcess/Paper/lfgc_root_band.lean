module

public import SubdiffusiveProcess.Paper.lfgc_root_impl
public import SubdiffusiveProcess.Lfgc.Window
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Band approximation of the root statistic (application of lem_band)

For the infrared field `H` the root statistic `aux_lfgc_root_impl_rootX` has, at every band index `h ≥ 1`, an
approximant with values in `[0,1]`, measurable for the layer window
`[-n - width(h+1), -n + width(h+1)]`, with `L^p` error `C_p δ^c 3^{-a h}`.
This is `SubdiffusiveProcess.Paper.lem_band` with zero score weights and the saturated statistic `aux_lfgc_root_stat_phiStat`.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_root_band_clip01_mem (x : ℝ) : max 0 (min 1 x) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem aux_lfgc_root_band_abs_sub_clip01_le {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |x - max 0 (min 1 y)| ≤ |x - y| := by
  obtain ⟨h0, h1⟩ := hx
  rcases le_total y 0 with hy | hy
  · rw [min_eq_right (hy.trans zero_le_one), max_eq_left hy]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rcases le_total y 1 with hy1 | hy1
    · rw [min_eq_right hy1, max_eq_right hy]
    · rw [min_eq_left hy1, max_eq_right zero_le_one]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_root_band_rootX_mem
    [_portSection0 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection1 : BorelSpace C(SpatialCoordinates d, ℝ)] [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (sigma : ℝ) (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ)
    (n : ℤ) (z : SpatialCoordinates d) {K : ℝ} (hK : 0 ≤ K)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) :
    aux_lfgc_root_impl_rootX I M sigma T offset shift N n z K H omega ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨aux_lfgc_root_stat_phiStat_nonneg K hK _, aux_lfgc_root_stat_phiStat_le_one K _⟩

/-- Band approximation of the root statistic. -/
theorem lfgc_root_band (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sobolev : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) :
    ∃ a c : ℝ, ∃ width : ℕ, 0 < a ∧ 0 < c ∧ 0 < width ∧
      ∀ p : ℝ, 1 ≤ p → ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
        ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
        ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg),
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
          (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
          (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
            _root_.SubdiffusiveProcess.Paper.primitive_scores d M sigma eps (eta N omega)
              (fun m y => F N m y omega) (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) →
          (∀ i : Fin T, n + offset i ≤ (N : ℤ)) →
          ∀ h : ℕ, 1 ≤ h →
            ∃ Y : BilateralField d → ℝ,
              StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
                (Set.Icc (-n - (width * (h + 1) : ℕ)) (-n + (width * (h + 1) : ℕ)))] Y ∧
              (∀ omega, Y omega ∈ Set.Icc (0 : ℝ) 1) ∧
              eLpNorm (fun omega => aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega - Y omega)
                (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
                ENNReal.ofReal (Cp * M.delta ^ c * (3 : ℝ) ^ (-(a * (h : ℝ)))) := by
  obtain ⟨CD, deltaD, hCD, hbase⟩ := Dbase sigma eps hsigma heps
  have hK : 0 ≤ 2 / θ₀ := by positivity
  obtain ⟨a, c, width, ha, hc, hw, hband⟩ := _root_.SubdiffusiveProcess.Paper.lem_band d hd I Poincare Extension MeyersMorrey
    Sobolev D Cresp hCresp sigma sigma eps hsigma hsigma heps T offset shift (fun _ => 0)
    (fun _ => le_rfl) (Real.toNNReal (2 / θ₀)) (aux_lfgc_root_stat_phiStat (2 / θ₀))
    (aux_lfgc_root_stat_phiStat_lipschitz (2 / θ₀) hK T) (aux_lfgc_root_stat_phiStat_zero (2 / θ₀) T) (aux_lfgc_root_stat_phiStat_nonneg (2 / θ₀) hK) CD
    (fun p hp => (hCD p hp).1)
  refine ⟨a, c, width, ha, hc, hw, fun p hp => ?_⟩
  obtain ⟨q, δ0, Cp, _, hq1, hδ0, hCp, hmain⟩ := hband p hp
  refine ⟨min δ0 (min 1 (deltaD q)), Cp, lt_min hδ0 (lt_min one_pos (hCD q hq1).2), hCp, ?_⟩
  intro M hM Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Zs rawGood hPrim N n z hnN hoff h hh
  have hDb := hbase q hq1 M (hM.trans (min_le_right _ _)) eta hEta F Praw Rraw Draw Zs rawGood hPrim
  obtain ⟨-, hX⟩ := hmain M (hM.trans (min_le_left _ _)) Rm hRm Sreg It H hH eta hEta F Praw Rraw
    Draw Zs rawGood hPrim hDb (fun n => by positivity) (fun n w => aux_lfgc_root_stat_unitCoeff n w)
    (fun n w => aux_lfgc_root_stat_unitCoeff_val n w)
  obtain ⟨Xb, hXbm, hXb⟩ := hX N n z hnN hoff h hh
  set Y0 := hXbm.mk Xb
  refine ⟨fun omega => max 0 (min 1 (Y0 omega)), ?_, fun omega => aux_lfgc_root_band_clip01_mem _, ?_⟩
  · have hm := hXbm.stronglyMeasurable_mk.measurable
    exact (measurable_const.max (measurable_const.min hm)).stronglyMeasurable
  · refine le_trans ?_ hXb
    have hrestriction : Measurable (fun omega : BilateralField d =>
        fun j : Set.Icc (-n - (width * (h + 1) : ℕ))
          (-n + (width * (h + 1) : ℕ)) => omega (j : ℤ)) :=
      Measurable.of_eval fun j => measurable_pi_apply (j : ℤ)
    have hXbm_full := hXbm.mono hrestriction.comap_le
    have hdiff := aestronglyMeasurable_of_eLpNorm_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hXb)
    have hroot : AEStronglyMeasurable (fun omega =>
        aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega)
        (chaosSampleLaw M).toMeasure := by
      have hm := hdiff.add hXbm_full
      apply hm.congr
      filter_upwards [] with omega
      simp only [Pi.add_apply, sub_add_cancel, zero_mul, zero_add, aux_lfgc_root_impl_rootX]
      rfl
    have hY0 : AEStronglyMeasurable Y0 (chaosSampleLaw M).toMeasure :=
      hXbm.stronglyMeasurable_mk.aestronglyMeasurable.mono hrestriction.comap_le
    refine eLpNorm_mono_ae (hroot.sub (aemeasurable_const.max
      (aemeasurable_const.min hY0.aemeasurable)).aestronglyMeasurable) ?_
    filter_upwards [hXbm.ae_eq_mk] with omega hom
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hmem := aux_lfgc_root_band_rootX_mem I M sigma T offset shift N n z hK H omega
    refine (aux_lfgc_root_band_abs_sub_clip01_le hmem).trans (le_of_eq ?_)
    rw [show Y0 omega = Xb omega from hom.symm]
    congr 1
    simp only [zero_mul, zero_add, aux_lfgc_root_impl_rootX]
    rfl

end SubdiffusiveProcess.Paper
