module

public import SubdiffusiveProcess.Paper.lfgc_root_band

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Band approximation of one prefix aux_lfgc_sum_band_summand (application of lem_band)

The prefix aux_lfgc_sum_band_summand at physical level `j ≤ N` and centre `w` is the drift score
`(Draw N (N-j) (3^N w)).toReal` (for `useD = true`) or the bad score `Z N (N-j) (3^N w)`
(for `useD = false`).  lem_band with score weights `(1,0,0,0)`, respectively `(0,1,1,1)`, no
roots and zero statistic gives, at every band index `h ≥ 1`, an approximant measurable for the
layer window `[-j - width(h+1), -j + width(h+1)]` with `L^p` error `C_p δ^c 3^{-a h}`.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- One prefix aux_lfgc_sum_band_summand. -/
noncomputable def aux_lfgc_sum_band_summand (useD : Bool)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (N : ℕ) (j : ℤ) (w : SpatialCoordinates d) (omega : BilateralField d) : ℝ :=
  if useD then (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega).toReal
  else Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega

/-- The lem_band score weights selecting one aux_lfgc_sum_band_summand. -/
def aux_lfgc_sum_band_summandWeight (useD : Bool) : Fin 4 → ℝ :=
  fun i => if useD then (if i = 0 then 1 else 0) else (if i = 0 then 0 else 1)

theorem aux_lfgc_sum_band_summandWeight_nonneg (useD : Bool) (i : Fin 4) : 0 ≤ aux_lfgc_sum_band_summandWeight useD i := by
  unfold aux_lfgc_sum_band_summandWeight
  split_ifs <;> norm_num

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_sum_band_zeroPhi_lipschitz :
    LipschitzWith 0 (fun _ : (Fin 0 → (Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)) → ℝ) =>
      (0 : ℝ)) :=
  LipschitzWith.const 0

/-- Band approximation of one prefix aux_lfgc_sum_band_summand. -/
theorem lfgc_sum_band (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sobolev : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d) (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (useD : Bool) :
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
        ∀ (N : ℕ) (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
          ∀ h : ℕ, 1 ≤ h →
            ∃ Y : BilateralField d → ℝ,
              StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
                (Set.Icc (-j - (width * (h + 1) : ℕ)) (-j + (width * (h + 1) : ℕ)))] Y ∧
              eLpNorm (fun omega => aux_lfgc_sum_band_summand useD Draw Z N j w omega - Y omega)
                (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
                ENNReal.ofReal (Cp * M.delta ^ c * (3 : ℝ) ^ (-(a * (h : ℝ)))) := by
  obtain ⟨CD, deltaD, hCD, hbase⟩ := Dbase sigma eps hsigma heps
  obtain ⟨a, c, width, ha, hc, hw, hband⟩ := _root_.SubdiffusiveProcess.Paper.lem_band d hd I Poincare Extension MeyersMorrey
    Sobolev D Cresp hCresp sigma sigma eps hsigma hsigma heps 0 (fun i => i.elim0)
    (fun i => i.elim0) (aux_lfgc_sum_band_summandWeight useD) (aux_lfgc_sum_band_summandWeight_nonneg useD) 0 (fun _ => 0)
    aux_lfgc_sum_band_zeroPhi_lipschitz rfl (fun _ => le_rfl) CD (fun p hp => (hCD p hp).1)
  refine ⟨a, c, width, ha, hc, hw, fun p hp => ?_⟩
  obtain ⟨q, δ0, Cp, _, hq1, hδ0, hCp, hmain⟩ := hband p hp
  refine ⟨min δ0 (min 1 (deltaD q)), Cp, lt_min hδ0 (lt_min one_pos (hCD q hq1).2), hCp, ?_⟩
  intro M hM Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Zs rawGood hPrim N j w hjN h hh
  have hDb := hbase q hq1 M (hM.trans (min_le_right _ _)) eta hEta F Praw Rraw Draw Zs rawGood hPrim
  obtain ⟨-, hX⟩ := hmain M (hM.trans (min_le_left _ _)) Rm hRm Sreg It H hH eta hEta F Praw Rraw
    Draw Zs rawGood hPrim hDb (fun n => by positivity) (fun n w => aux_lfgc_root_stat_unitCoeff n w)
    (fun n w => aux_lfgc_root_stat_unitCoeff_val n w)
  obtain ⟨Xb, hXbm, hXb⟩ := hX N j w hjN (fun i => i.elim0) h hh
  refine ⟨hXbm.mk Xb, hXbm.stronglyMeasurable_mk, le_trans (le_of_eq ?_) hXb⟩
  refine eLpNorm_congr_ae ?_
  filter_upwards [hXbm.ae_eq_mk, hPrim] with omega hom hp
  rw [← hom]
  congr 1
  obtain ⟨-, -, -, -, -, -, -, -, -, h7, -⟩ := hp N
  have h7' := (h7 ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w)).1
  simp only at h7'
  cases useD
  · simp only [aux_lfgc_sum_band_summand, aux_lfgc_sum_band_summandWeight, Bool.false_eq_true, ite_false]
    rw [h7']
    simp
  · simp only [aux_lfgc_sum_band_summand, aux_lfgc_sum_band_summandWeight, ite_true]
    simp

end SubdiffusiveProcess.Paper
