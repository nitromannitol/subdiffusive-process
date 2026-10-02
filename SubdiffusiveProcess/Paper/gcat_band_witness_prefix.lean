import SubdiffusiveProcess.Paper.gcat_band_witness_prefix_core2
import SubdiffusiveProcess.Paper.gcat_prefix_limits
import SubdiffusiveProcess.Paper.lem_band
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Paper.primitive_scores
import SubdiffusiveProcess.Paper.prefix_physical_tail

/-! # `gcat_band_witness_prefix`: interval-event cover of the failure of the prefix conditions of a good cell

For a catalogue cell of level `k` and centre `z`, and limit arrays `ZLim`, `DLim` that are the limits in measure of
the catalogue prefixes `gcat_prefix` (exactly the arrays of `gcat_prefix_limits`), the failure of the conditions
`ZLim U D code < lambdaLim * D ∧ DLim U D code < lambdaLim * D` (all roots `U`, all `D ≥ k0`, all codes) is almost surely
covered by band-measurable events `W_h` (band `σ(ω_{-j} : k-h ≤ j ≤ k+2h)`) with `P(W_h) ≤ exp(-A h)`.
The disorder threshold is produced before the model, the cell and the arrays.
Proof: `lem_band` (Z/D banks) + `lem_prefix_limit` (limit terms, exceedance passage) + `prefix_physical_tail` (finite tails)
+ the abstract cover `gcat_band_witness_prefix_core2`. -/

open MeasureTheory Filter Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper
/-- Layer window `σ(ω_j : -n - w(h+1) ≤ j ≤ -n + w(h+1))` of `lem_band`, as a σ-field. -/
def aux_gcat_band_witness_lbWindow (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (n : ℤ) (w h : ℕ) : MeasurableSpace (BilateralField d) :=
  MeasurableSpace.comap
    (fun omega : BilateralField d =>
      fun j : Set.Icc (-n - ((w * (h + 1) : ℕ) : ℤ)) (-n + ((w * (h + 1) : ℕ) : ℤ)) => omega (j : ℤ))
    inferInstance

theorem aux_gcat_band_witness_restrict_congr (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    {s t : Set ℤ} (h : s = t) :
    MeasurableSpace.comap (fun (omega : BilateralField d) (j : s) => omega (j : ℤ))
        (inferInstance : MeasurableSpace ((j : s) → C(SpatialCoordinates d, ℝ))) =
      MeasurableSpace.comap (fun (omega : BilateralField d) (j : t) => omega (j : ℤ))
        (inferInstance : MeasurableSpace ((j : t) → C(SpatialCoordinates d, ℝ))) := by
  subst h; rfl

/-- `lem_band`'s window is the layer band `Bsig (n - w(h+1)) (n + w(h+1))`. -/
theorem aux_gcat_band_witness_lbWindow_eq (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (n : ℤ) (w h : ℕ) :
    aux_gcat_band_witness_lbWindow d n w h =
      aux_gcat_band_condexp_Bsig d (n - ((w * (h + 1) : ℕ) : ℤ)) (n + ((w * (h + 1) : ℕ) : ℤ)) := by
  rw [aux_gcat_band_condexp_Bsig_eq]
  unfold aux_gcat_band_witness_lbWindow
  exact aux_gcat_band_witness_restrict_congr d (by
    ext x
    simp only [Set.mem_Icc]
    omega)

/-- The constant coefficient `1` on any open set, as an element of `PositiveCoefficient`. -/
def aux_gcat_band_witness_unitA (d : ℕ) (Ω : TopologicalSpace.Opens (SpatialCoordinates d)) :
    PositiveCoefficient Ω :=
  ⟨(memLp_top_const (1 : ℝ)).toLp (fun _ => (1 : ℝ)), 1, one_pos, by
    filter_upwards [(memLp_top_const (1 : ℝ) : MemLp (fun _ : SpatialCoordinates d => (1 : ℝ)) ∞
      (volume.restrict (Ω : Set (SpatialCoordinates d)))).coeFn_toLp] with x hx
    rw [hx]⟩

theorem aux_gcat_band_witness_unitA_ae (d : ℕ) (Ω : TopologicalSpace.Opens (SpatialCoordinates d)) :
    (aux_gcat_band_witness_unitA d Ω).val =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      (fun _ => (1 : ℝ)) :=
  (memLp_top_const (1 : ℝ) : MemLp (fun _ : SpatialCoordinates d => (1 : ℝ)) ∞
      (volume.restrict (Ω : Set (SpatialCoordinates d)))).coeFn_toLp

/-- Band approximants of the finite-cutoff bad score `Z`, from `lem_band` (weights `(0,1,1,1)`, no test). -/
theorem aux_gcat_band_witness_bank_Z
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (Dbase : Paper.sum_errors_baseline_input d)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ a c : ℝ, ∃ width : ℕ, 0 < a ∧ 0 < c ∧ 0 < width ∧
      ∀ p : ℝ, 1 ≤ p → ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
        ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
          (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
          (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega) (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) → ∀ h : ℕ, 1 ≤ h →
          ∃ Yn : BilateralField d → ℝ,
            AEStronglyMeasurable[aux_gcat_band_witness_lbWindow d n width h] Yn
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun omega => Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega - Yn omega)
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (Cp * M.delta ^ c * (3 : ℝ) ^ (-(a * (h : ℝ)))) := by
  classical
  obtain ⟨CD, deltaD, hCDdD, hbase⟩ := Dbase s eps hs heps
  obtain ⟨a, c, width, ha, hc, hw, hmain⟩ :=
    Paper.lem_band d hd I Pc Xc W Sf Dd Cresp hCresp s sigma eps hs hsigma heps 0
      (fun i => i.elim0) (fun i => i.elim0) ![0, 1, 1, 1]
      (by intro i; fin_cases i <;> simp) 0 (fun _ => 0) (LipschitzWith.const 0) rfl
      (fun _ => le_refl 0) CD (fun p hp => (hCDdD p hp).1)
  refine ⟨a, c, width, ha, hc, hw, fun p hp => ?_⟩
  obtain ⟨q, delta0, Cp, hq2, hq1, hd0, hCp, hM⟩ := hmain p hp
  refine ⟨min delta0 (min 1 (deltaD q)), Cp, lt_min hd0 (lt_min one_pos (hCDdD q hq1).2), hCp, ?_⟩
  intro M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim N n z hn h hh
  have hM1 : M.delta ≤ delta0 := hMd.trans (min_le_left _ _)
  have hM2 : M.delta ≤ min 1 (deltaD q) := hMd.trans (min_le_right _ _)
  have hDb := hbase q hq1 M hM2 eta heta F Praw Rraw Draw Z rawGood hprim
  let sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n) := fun n => zpow_pos (by norm_num) _
  obtain ⟨-, hmain2⟩ := hM M hM1 Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim hDb
    sidePos (fun n z => aux_gcat_band_witness_unitA d _) (fun n z => aux_gcat_band_witness_unitA_ae d _)
  obtain ⟨Xband, hXm, hXe⟩ := hmain2 N n z hn (fun i => i.elim0) h hh
  refine ⟨Xband, hXm, ?_⟩
  refine le_trans (le_of_eq ?_) hXe
  apply eLpNorm_congr_ae
  filter_upwards [hprim] with omega hps
  obtain ⟨_, _, _, _, _, _, _, _, _, hZ, _⟩ := hps N
  have hz := (hZ ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)).1
  dsimp only at hz
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, zero_mul, one_mul, zero_add, add_zero]
  rw [hz]

/-- Band approximants of the finite-cutoff error score `D`, from `lem_band` (weights `(1,0,0,0)`, no test). -/
theorem aux_gcat_band_witness_bank_D
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (Dbase : Paper.sum_errors_baseline_input d)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ a c : ℝ, ∃ width : ℕ, 0 < a ∧ 0 < c ∧ 0 < width ∧
      ∀ p : ℝ, 1 ≤ p → ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
        ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
          (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
          (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega) (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) → ∀ h : ℕ, 1 ≤ h →
          ∃ Yn : BilateralField d → ℝ,
            AEStronglyMeasurable[aux_gcat_band_witness_lbWindow d n width h] Yn
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun omega => (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal - Yn omega)
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (Cp * M.delta ^ c * (3 : ℝ) ^ (-(a * (h : ℝ)))) := by
  classical
  obtain ⟨CD, deltaD, hCDdD, hbase⟩ := Dbase s eps hs heps
  obtain ⟨a, c, width, ha, hc, hw, hmain⟩ :=
    Paper.lem_band d hd I Pc Xc W Sf Dd Cresp hCresp s sigma eps hs hsigma heps 0
      (fun i => i.elim0) (fun i => i.elim0) ![1, 0, 0, 0]
      (by intro i; fin_cases i <;> simp) 0 (fun _ => 0) (LipschitzWith.const 0) rfl
      (fun _ => le_refl 0) CD (fun p hp => (hCDdD p hp).1)
  refine ⟨a, c, width, ha, hc, hw, fun p hp => ?_⟩
  obtain ⟨q, delta0, Cp, hq2, hq1, hd0, hCp, hM⟩ := hmain p hp
  refine ⟨min delta0 (min 1 (deltaD q)), Cp, lt_min hd0 (lt_min one_pos (hCDdD q hq1).2), hCp, ?_⟩
  intro M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim N n z hn h hh
  have hM1 : M.delta ≤ delta0 := hMd.trans (min_le_left _ _)
  have hM2 : M.delta ≤ min 1 (deltaD q) := hMd.trans (min_le_right _ _)
  have hDb := hbase q hq1 M hM2 eta heta F Praw Rraw Draw Z rawGood hprim
  let sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n) := fun n => zpow_pos (by norm_num) _
  obtain ⟨-, hmain2⟩ := hM M hM1 Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim hDb
    sidePos (fun n z => aux_gcat_band_witness_unitA d _) (fun n z => aux_gcat_band_witness_unitA_ae d _)
  obtain ⟨Xband, hXm, hXe⟩ := hmain2 N n z hn (fun i => i.elim0) h hh
  refine ⟨Xband, hXm, ?_⟩
  refine le_trans (le_of_eq ?_) hXe
  apply eLpNorm_congr_ae
  refine Filter.Eventually.of_forall (fun omega => ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, zero_mul, one_mul, add_zero]


/-- Weakening of a finite-cutoff band approximation: smaller decay rate, smaller exponent of the
disorder (for `δ ≤ 1`), wider band, larger constant. -/
theorem aux_gcat_band_witness_band_weaken
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hM1 : M.delta ≤ 1)
    {p : ℝ} {Xf : BilateralField d → ℝ} {n : ℤ}
    {w0 w : ℕ} (hw : w0 ≤ w) {a0 a c0 c : ℝ} (ha : a ≤ a0) (hc : c ≤ c0)
    {C0 C : ℝ} (hC : C0 ≤ C) (hC0 : 0 ≤ C0) (h : ℕ)
    (hex : ∃ Yn : BilateralField d → ℝ,
      AEStronglyMeasurable[aux_gcat_band_witness_lbWindow d n w0 h] Yn (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Xf om - Yn om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C0 * M.delta ^ c0 * (3 : ℝ) ^ (-(a0 * (h : ℝ))))) :
    ∃ Yn : BilateralField d → ℝ,
      AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - ((w * (h + 1) : ℕ) : ℤ))
        (n + ((w * (h + 1) : ℕ) : ℤ))] Yn (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Xf om - Yn om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C * M.delta ^ c * (3 : ℝ) ^ (-(a * (h : ℝ)))) := by
  obtain ⟨Yn, hYm, hYe⟩ := hex
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hsub : Set.Icc (n - ((w0 * (h + 1) : ℕ) : ℤ)) (n + ((w0 * (h + 1) : ℕ) : ℤ)) ⊆
      Set.Icc (n - ((w * (h + 1) : ℕ) : ℤ)) (n + ((w * (h + 1) : ℕ) : ℤ)) := by
    have hle : ((w0 * (h + 1) : ℕ) : ℤ) ≤ ((w * (h + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_right (h + 1) hw
    intro x hx
    simp only [Set.mem_Icc] at hx ⊢
    constructor <;> omega
  have hmono : aux_gcat_band_condexp_Bsig d (n - ((w0 * (h + 1) : ℕ) : ℤ)) (n + ((w0 * (h + 1) : ℕ) : ℤ)) ≤
      aux_gcat_band_condexp_Bsig d (n - ((w * (h + 1) : ℕ) : ℤ)) (n + ((w * (h + 1) : ℕ) : ℤ)) :=
    aux_neg_restrict_mono (E := C(SpatialCoordinates d, ℝ)) hsub
  refine ⟨Yn, ?_, hYe.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · rw [aux_gcat_band_witness_lbWindow_eq] at hYm
    exact hYm.mono hmono
  · have h1 : M.delta ^ c0 ≤ M.delta ^ c := Real.rpow_le_rpow_of_exponent_ge hdpos hM1 hc
    have h2 : (3 : ℝ) ^ (-(a0 * (h : ℝ))) ≤ (3 : ℝ) ^ (-(a * (h : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : a * (h : ℝ) ≤ a0 * (h : ℝ) := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg h)
      linarith
    have h3 : 0 ≤ M.delta ^ c0 := Real.rpow_nonneg hdpos.le _
    have h4 : 0 ≤ (3 : ℝ) ^ (-(a0 * (h : ℝ))) := Real.rpow_nonneg (by norm_num) _
    have h5 : 0 ≤ M.delta ^ c := Real.rpow_nonneg hdpos.le _
    have h6 : 0 ≤ (3 : ℝ) ^ (-(a * (h : ℝ))) := Real.rpow_nonneg (by norm_num) _
    exact mul_le_mul (mul_le_mul hC h1 h3 (hC0.trans hC)) h2 h4 (mul_nonneg (hC0.trans hC) h5)

/-- The cutoff-`N` score of a tag (`true`: error score `D`; `false`: bad score `Z`) at scale `n` and centre
`z`, zero for scales finer than the cutoff (the convention of `lem_prefix_limit`'s `value`). -/
def aux_gcat_band_witness_gscore {d : ℕ}
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞) (tag : Bool) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (omega : BilateralField d) : ℝ :=
  if n ≤ (N : ℤ) then
    (if tag then (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal
     else Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega)
  else 0

/-- Band approximation of the guarded score along a cutoff sequence tending to infinity, combining the
two `lem_band` banks (`Z`-type and `D`-type) into one set of constants. -/
theorem aux_gcat_band_witness_prefix_hband
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hM1 : M.delta ≤ 1) (p : ℝ)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
    (aZ cZ aD cD CpZ CpD : ℝ) (wZ wD : ℕ) (a c Cp' : ℝ) (Cband : ℕ)
    (haZ : a ≤ aZ) (haD : a ≤ aD) (hcZ : c ≤ cZ) (hcD : c ≤ cD) (hCZ : CpZ ≤ Cp') (hCD : CpD ≤ Cp')
    (hCZ0 : 0 ≤ CpZ) (hCD0 : 0 ≤ CpD) (hwZ : wZ ≤ Cband) (hwD : wD ≤ Cband)
    (hZbank : ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) → ∀ h : ℕ, 1 ≤ h →
      ∃ Yn : BilateralField d → ℝ,
        AEStronglyMeasurable[aux_gcat_band_witness_lbWindow d n wZ h] Yn (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega => Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega - Yn omega)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (CpZ * M.delta ^ cZ * (3 : ℝ) ^ (-(aZ * (h : ℝ)))))
    (hDbank : ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) → ∀ h : ℕ, 1 ≤ h →
      ∃ Yn : BilateralField d → ℝ,
        AEStronglyMeasurable[aux_gcat_band_witness_lbWindow d n wD h] Yn (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega => (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal - Yn omega)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (CpD * M.delta ^ cD * (3 : ℝ) ^ (-(aD * (h : ℝ)))))
    (n : ℤ) (z : SpatialCoordinates d) (tag : Bool) (phi : ℕ → ℕ)
    (hphi : Tendsto phi atTop atTop) (H : ℕ) (hH : 1 ≤ H) :
    ∀ᶠ kk in atTop, ∃ Yn : BilateralField d → ℝ,
      AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - ((Cband * (H + 1) : ℕ) : ℤ))
        (n + ((Cband * (H + 1) : ℕ) : ℤ))] Yn (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun omega => aux_gcat_band_witness_gscore Z Draw tag (phi kk) n z omega - Yn omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cp' * M.delta ^ c * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
  have hev : ∀ᶠ kk in atTop, n ≤ (phi kk : ℤ) := by
    have h1 : ∀ᶠ kk in atTop, n.toNat ≤ phi kk := hphi.eventually_ge_atTop _
    filter_upwards [h1] with kk hkk
    have : n ≤ (n.toNat : ℤ) := Int.self_le_toNat n
    exact this.trans (by exact_mod_cast hkk)
  filter_upwards [hev] with kk hkk
  unfold aux_gcat_band_witness_gscore
  cases tag
  · simp only [hkk, if_true, Bool.false_eq_true, if_false]
    exact aux_gcat_band_witness_band_weaken d M hM1 hwZ haZ hcZ hCZ hCZ0 H (hZbank (phi kk) n z hkk H hH)
  · simp only [hkk, if_true]
    exact aux_gcat_band_witness_band_weaken d M hM1 hwD haD hcD hCD hCD0 H (hDbank (phi kk) n z hkk H hH)




/-- The catalogue roots `Enl × Shift`. -/
abbrev aux_gcat_band_witness_Roots (d : ℕ) := Fin 3 × (Fin d → Fin 3)

/-- Observation codes of depth `D` (descendants or roots). -/
abbrev aux_gcat_band_witness_Code (d D : ℕ) :=
  (Fin D → OddGridIndex d 1) ⊕ aux_gcat_band_witness_Roots d

open Finset in
theorem aux_gcat_band_witness_sum_range_eq_sum_Icc (f : ℤ → ℝ) (a : ℤ) (D cbuf : ℕ) :
    ∑ j ∈ Finset.range (D + cbuf + 1), f (a - (cbuf : ℤ) + (j : ℤ)) =
      ∑ t ∈ Finset.Icc (a - (cbuf : ℤ)) (a + (D : ℤ)), f t := by
  have h : ∀ n : ℕ, ∑ j ∈ Finset.range n, f (a - (cbuf : ℤ) + (j : ℤ)) =
      ∑ t ∈ Finset.Ico (a - (cbuf : ℤ)) (a - (cbuf : ℤ) + (n : ℤ)), f t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        have : Finset.Ico (a - (cbuf : ℤ)) (a - (cbuf : ℤ) + ((n + 1 : ℕ) : ℤ)) =
            insert (a - (cbuf : ℤ) + (n : ℤ)) (Finset.Ico (a - (cbuf : ℤ)) (a - (cbuf : ℤ) + (n : ℤ))) := by
          ext x
          simp only [Finset.mem_Ico, Finset.mem_insert]
          push_cast
          omega
        rw [this, Finset.sum_insert (by simp), add_comm]
  rw [h]
  congr 1
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  push_cast
  omega

theorem aux_gcat_band_witness_sum_Icc_le_of_zero_above (g : ℤ → ℝ) (hnn : ∀ j, 0 ≤ g j) (N a b c : ℤ) (hc : 0 ≤ c)
    (hz : ∀ j, N < j → g j = 0) :
    ∑ j ∈ Finset.Icc a b, g j ≤ ∑ j ∈ Finset.Icc a (min N (b + c)), g j := by
  have h1 : ∑ j ∈ Finset.Icc a b, g j = ∑ j ∈ (Finset.Icc a b).filter (fun j => j ≤ N), g j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : j ≤ N
    · simp [hj]
    · simp [hj, hz j (lt_of_not_ge hj)]
  rw [h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hnn j)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff] at hx ⊢
  omega

/-- The finite-cutoff tail of the window sums of the catalogue prefix, from `prefix_physical_tail`. -/
theorem aux_gcat_band_witness_prefix_tail_finite
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s eps lam A0 : ℝ) (cbuf gH k : ℕ)
    (z : SpatialCoordinates d)
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hprim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (hphys : ∀ (N k D : ℕ), 1 ≤ D → ∀ (e : ℕ) (w : SpatialCoordinates d) (useD : Bool),
      (chaosSampleLaw M).toMeasure {om | lam * (D : ℝ) / 4 <
        aux_prefix_physical_tail_sum N k cbuf D e w Z Draw useD om} ≤
        ENNReal.ofReal (2 * Real.exp (-(A0 * (D : ℝ)))))
    (N : ℕ) (U : aux_gcat_band_witness_Roots d) (D : ℕ) (hD : 1 ≤ D)
    (code : aux_gcat_band_witness_Code d D) (tag : Bool) :
    (chaosSampleLaw M).toMeasure {om | lam * (D : ℝ) / 4 <
      ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
        aux_gcat_band_witness_gscore Z Draw tag N j (gcat_obsCentre gH k z U D code) om} ≤
      ENNReal.ofReal (2 * Real.exp (-(A0 * (D : ℝ)))) := by
  classical
  refine le_trans (measure_mono_ae ?_) (hphys N k D hD (gcat_factor gH U.1)
    (gcat_obsCentre gH k z U D code) tag)
  filter_upwards [hprim] with om hps
  intro hlarge
  have hZnn : ∀ m y, 0 ≤ Z N m y om := by
    intro m y
    obtain ⟨_, _, _, _, _, _, _, _, _, hZ, _⟩ := hps N
    exact (hZ m y).2.1
  -- pointwise description of the summand
  let g : ℤ → ℝ := fun j =>
    if 0 ≤ (N : ℤ) - j then
      (if tag then (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • gcat_obsCentre gH k z U D code) om).toReal
       else Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • gcat_obsCentre gH k z U D code) om)
    else 0
  have hg : ∀ j, aux_gcat_band_witness_gscore Z Draw tag N j (gcat_obsCentre gH k z U D code) om
      = g j := by
    intro j
    simp only [aux_gcat_band_witness_gscore, g, sub_nonneg]
  have hgnn : ∀ j, 0 ≤ g j := by
    intro j
    simp only [g]
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact hZnn _ _
    · exact le_refl 0
  have hgz : ∀ j, (N : ℤ) < j → g j = 0 := by
    intro j hj
    simp only [g]
    rw [if_neg (by omega)]
  have hle : ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)), g j ≤
      aux_prefix_physical_tail_sum N k cbuf D (gcat_factor gH U.1) (gcat_obsCentre gH k z U D code)
        Z Draw tag om := by
    have hbase := aux_gcat_band_witness_sum_Icc_le_of_zero_above g hgnn (N : ℤ)
      (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)) (cbuf : ℤ)
      (Int.natCast_nonneg _) hgz
    refine hbase.trans (le_of_eq ?_)
    unfold aux_prefix_physical_tail_sum
    have hlev : gcat_rootLevel gH k U = (k : ℤ) - (gcat_factor gH U.1 : ℤ) := rfl
    rw [hlev]
  refine lt_of_lt_of_le hlarge ?_
  simp only [hg]
  exact hle

theorem aux_gcat_band_witness_prefix_constants
    (Cband cbuf k0 c0 : ℕ) (hk0 : 1 ≤ k0) (beta v Cgeom a : ℝ)
    (hCgeom : 1 ≤ Cgeom) (ha : 0 < a) :
    ∃ Atail p : ℝ, 0 < Atail ∧ 2 ≤ p ∧ 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ Atail ∧
      64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ p * a * Real.log 3 ∧
      Real.log (9 * Cgeom * Real.exp (Atail * ((cbuf : ℝ) + 1))) + beta * ((Cband : ℝ) + (c0 : ℝ)) ≤
        (Atail - v - beta * ((Cband : ℝ) + 1)) * (((k0 + cbuf + 1 : ℕ)) : ℝ) := by
  set X : ℝ := 64 * ((Cband : ℝ) + 1) * (beta + v + 1) with hX
  have hk0r : (1 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk0
  set R : ℝ := Real.log (9 * Cgeom) + beta * ((Cband : ℝ) + (c0 : ℝ)) +
    (v + beta * ((Cband : ℝ) + 1)) * ((k0 : ℝ) + (cbuf : ℝ) + 1) with hR
  set Atail : ℝ := max (max X (R / (k0 : ℝ))) 1 with hAtail
  have hAge1 : 1 ≤ Atail := le_max_right _ _
  have hAgeX : X ≤ Atail := (le_max_left _ _).trans (le_max_left _ _)
  have hAgeR : R / (k0 : ℝ) ≤ Atail := (le_max_right _ _).trans (le_max_left _ _)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpos9 : 0 < 9 * Cgeom := by positivity
  refine ⟨Atail, max 2 (X / (a * Real.log 3)), by linarith, le_max_left _ _, hAgeX, ?_, ?_⟩
  · have hal : 0 < a * Real.log 3 := mul_pos ha hlog3
    have h1 : X / (a * Real.log 3) ≤ max 2 (X / (a * Real.log 3)) := le_max_right _ _
    calc X = X / (a * Real.log 3) * (a * Real.log 3) := by field_simp
      _ ≤ max 2 (X / (a * Real.log 3)) * (a * Real.log 3) := mul_le_mul_of_nonneg_right h1 hal.le
      _ = max 2 (X / (a * Real.log 3)) * a * Real.log 3 := by ring
  · have hlogexp : Real.log (9 * Cgeom * Real.exp (Atail * ((cbuf : ℝ) + 1))) =
        Real.log (9 * Cgeom) + Atail * ((cbuf : ℝ) + 1) := by
      rw [Real.log_mul hpos9.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [hlogexp]
    have hAk : R ≤ Atail * (k0 : ℝ) := by
      have := mul_le_mul_of_nonneg_right hAgeR (by linarith : (0 : ℝ) ≤ (k0 : ℝ))
      calc R = R / (k0 : ℝ) * (k0 : ℝ) := by field_simp
        _ ≤ Atail * (k0 : ℝ) := this
    push_cast
    nlinarith [hAk]

/-- Positions of the prefix families: root, depth and observation code. -/
abbrev aux_gcat_band_witness_Pos (d : ℕ) :=
  aux_gcat_band_witness_Roots d × (Σ D : ℕ, aux_gcat_band_witness_Code d D)

/-- Limit bank of the prefix scores from `lem_prefix_limit` (no test entries): a subsequence along which the
guarded `Z`/`D` scores at every scale and every catalogue observation centre converge in `L^p`, together with
the window-sum convergence and the strict-margin exceedance passage. -/
theorem aux_gcat_band_witness_prefix_limit_bank
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (p : ℝ) (hp : 1 ≤ p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          primitive_scores d M s eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
      ∀ (gH cbuf k : ℕ) (z : SpatialCoordinates d) (phi : ℕ → ℕ), StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∃ V : aux_gcat_band_witness_Pos d → ℤ → Bool → BilateralField d → ℝ,
        (∀ (pos : aux_gcat_band_witness_Pos d) (j : ℤ) (tag : Bool), MemLp (V pos j tag) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ (N : ℕ) (pos : aux_gcat_band_witness_Pos d) (j : ℤ) (tag : Bool), MemLp (aux_gcat_band_witness_gscore Z Draw tag N j
          (gcat_obsCentre gH k z pos.1 pos.2.1 pos.2.2)) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure) ∧
        (∀ (pos : aux_gcat_band_witness_Pos d) (j : ℤ) (tag : Bool), Tendsto (fun kk => eLpNorm (fun ω =>
          aux_gcat_band_witness_gscore Z Draw tag (phi (psi kk)) j
            (gcat_obsCentre gH k z pos.1 pos.2.1 pos.2.2) ω - V pos j tag ω) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure) atTop (𝓝 0)) ∧
        (∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D) (tag : Bool),
          Tendsto (fun kk => eLpNorm (fun ω =>
            ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
              aux_gcat_band_witness_gscore Z Draw tag (phi (psi kk)) j
                (gcat_obsCentre gH k z U D code) ω -
            ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
              V ⟨U, ⟨D, code⟩⟩ j tag ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0)) ∧
        (∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D) (tag : Bool)
            (A a a' : ℝ), 0 < A → a < a' →
          (∀ n, (chaosSampleLaw M).toMeasure {ω | a <
            ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
              aux_gcat_band_witness_gscore Z Draw tag (phi n) j (gcat_obsCentre gH k z U D code) ω} ≤
            ENNReal.ofReal (Real.exp (-(A * (D : ℝ))))) →
          (chaosSampleLaw M).toMeasure {ω | a' <
            ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
              V ⟨U, ⟨D, code⟩⟩ j tag ω} ≤ ENNReal.ofReal (Real.exp (-(A * (D : ℝ))))) := by
  classical
  obtain ⟨q, delta0, K, hq1, hq2, hq3, hdelta0, hK, hM⟩ :=
    Paper.lem_prefix_limit d hd I Pc Xc W Sf Dd Cresp hCresp s sigma eps hs hsigma heps
      0 (fun i => i.elim0) (fun i => i.elim0) ({p} : Finset ℝ)
      (fun p' hp' => by rw [Finset.mem_singleton.mp hp']; exact hp)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim gH cbuf k z phi hphi
  obtain ⟨hRefPos, h12q, hPosAll⟩ := hM M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
    (fun n => zpow_pos (by norm_num : (0 : ℝ) < 3) (-n))
  obtain ⟨psi, hpsi, Vlim, hVm, hVmom, hvalmom, hLpConv, hPrefix⟩ :=
    hPosAll (aux_gcat_band_witness_Pos d) (fun _ => 0)
      (fun pos => gcat_obsCentre gH k z pos.1 pos.2.1 pos.2.2) phi hphi
  have hmem : p ∈ insert (1 : ℝ) ({p} : Finset ℝ) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self p)
  let test : Bool → (Fin 5 ⊕ (Fin 0 × (Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)))) :=
    fun tag => Sum.inl (if tag then 3 else 4)
  refine ⟨psi, hpsi, fun pos j tag => Vlim pos j (test tag), ?_, ?_, ?_, ?_, ?_⟩
  · intro pos j tag
    exact (hVmom p hmem pos j (test tag)).1
  · intro N pos j tag
    have h := (hvalmom p hmem N pos j (test tag)).1
    cases tag
    · simpa using h
    · simpa using h
  · intro pos j tag
    have h := hLpConv p hmem pos j (test tag)
    cases tag
    · simpa using h
    · simpa using h
  · intro U D code tag
    have h := (hPrefix ⟨U, ⟨D, code⟩⟩ (gcat_rootLevel gH k U) D cbuf (test tag)).2.1 p hmem
    cases tag
    · simpa using h.2
    · simpa using h.2
  · intro U D code tag A a a' hA haa' hfin
    have h := (hPrefix ⟨U, ⟨D, code⟩⟩ (gcat_rootLevel gH k U) D cbuf (test tag)).2.2 A a a' hA haa'
    cases tag
    · simpa using h (by simpa using hfin)
    · simpa using h (by simpa using hfin)

/-- The admissible true depths of a window of `D'` terms (`D + cbuf + 1 = D'`): at most one. -/
abbrev aux_gcat_band_witness_Depth (cbuf D' : ℕ) := {D0 : ℕ // D0 + cbuf + 1 = D'}

instance aux_gcat_band_witness_Depth_fintype (cbuf D' : ℕ) :
    Fintype (aux_gcat_band_witness_Depth cbuf D') :=
  haveI : Finite (aux_gcat_band_witness_Depth cbuf D') :=
    Finite.of_injective (fun x : aux_gcat_band_witness_Depth cbuf D' =>
      (⟨x.1, by have := x.2; omega⟩ : Fin (D' + 1))) (by
        intro x y hxy
        exact Subtype.ext (by simpa using congrArg Fin.val hxy))
  Fintype.ofFinite _

/-- Index type of the prefix family for windows of `D'` terms: score tag, root, depth `D' - cbuf - 1`
(as a subsingleton subtype, so that no casts are needed), code of that depth. -/
abbrev aux_gcat_band_witness_Idx (d cbuf D' : ℕ) :=
  Bool × aux_gcat_band_witness_Roots d ×
    Σ e : aux_gcat_band_witness_Depth cbuf D', aux_gcat_band_witness_Code d e.1

/-- The catalogue position of an index. -/
def aux_gcat_band_witness_posOf {d cbuf D' : ℕ} (i : aux_gcat_band_witness_Idx d cbuf D') :
    aux_gcat_band_witness_Pos d :=
  ⟨i.2.1, ⟨i.2.2.1.1, i.2.2.2⟩⟩

/-- Geometric growth of the index family: `card ≤ Cgeom * exp(v D')`. -/
theorem aux_gcat_band_witness_Idx_card (d cbuf D' : ℕ) :
    (Fintype.card (aux_gcat_band_witness_Idx d cbuf D') : ℝ) ≤
      (6 * (3 : ℝ) ^ d * (1 + 3 * (3 : ℝ) ^ d)) * Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) := by
  classical
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hE : (1 : ℝ) ≤ Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) := by
    apply Real.one_le_exp
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hpos : 0 ≤ (3 : ℝ) ^ d := by positivity
  -- each depth contributes at most `(1 + 3 * 3^d) * exp(v D')` codes
  have hcode : ∀ e : aux_gcat_band_witness_Depth cbuf D',
      (Fintype.card (aux_gcat_band_witness_Code d e.1) : ℝ) ≤
        (1 + 3 * (3 : ℝ) ^ d) * Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) := by
    intro e
    have hcard : (Fintype.card (aux_gcat_band_witness_Code d e.1) : ℝ) =
        ((3 : ℝ) ^ d) ^ e.1 + 3 * (3 : ℝ) ^ d := by
      simp only [aux_gcat_band_witness_Code, aux_gcat_band_witness_Roots, Fintype.card_sum,
        Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, OddGridIndex]
      push_cast
      ring
    rw [hcard]
    have hle : e.1 ≤ D' := by have := e.2; omega
    have hpow : ((3 : ℝ) ^ d) ^ e.1 ≤ Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) := by
      have h1 : ((3 : ℝ) ^ d) ^ e.1 ≤ ((3 : ℝ) ^ d) ^ D' := pow_le_pow_right₀ h3 hle
      refine h1.trans (le_of_eq ?_)
      rw [← pow_mul, show ((3 : ℝ) ^ (d * D')) = Real.exp (Real.log 3 * ((d * D' : ℕ) : ℝ)) by
        rw [Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]]
      congr 1
      push_cast
      ring
    calc ((3 : ℝ) ^ d) ^ e.1 + 3 * (3 : ℝ) ^ d
        ≤ Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) +
            3 * (3 : ℝ) ^ d * Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) :=
          add_le_add hpow (le_mul_of_one_le_right (by positivity) hE)
      _ = (1 + 3 * (3 : ℝ) ^ d) * Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) := by ring
  have hS : Fintype.card (aux_gcat_band_witness_Depth cbuf D') ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro a b
    exact Subtype.ext (by have := a.2; have := b.2; omega)
  have hsig : (Fintype.card (Σ e : aux_gcat_band_witness_Depth cbuf D',
      aux_gcat_band_witness_Code d e.1) : ℝ) ≤
      (1 + 3 * (3 : ℝ) ^ d) * Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) := by
    rw [Fintype.card_sigma]
    push_cast
    calc (∑ e : aux_gcat_band_witness_Depth cbuf D', (Fintype.card (aux_gcat_band_witness_Code d e.1) : ℝ))
        ≤ ∑ _e : aux_gcat_band_witness_Depth cbuf D',
            (1 + 3 * (3 : ℝ) ^ d) * Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) :=
          Finset.sum_le_sum (fun e _ => hcode e)
      _ = (Fintype.card (aux_gcat_band_witness_Depth cbuf D') : ℝ) *
            ((1 + 3 * (3 : ℝ) ^ d) * Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ))) := by
          simp
      _ ≤ 1 * ((1 + 3 * (3 : ℝ) ^ d) * Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ))) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hS
          · positivity
      _ = _ := one_mul _
  have hcardIdx : (Fintype.card (aux_gcat_band_witness_Idx d cbuf D') : ℝ) =
      2 * (3 * (3 : ℝ) ^ d) * (Fintype.card (Σ e : aux_gcat_band_witness_Depth cbuf D',
        aux_gcat_band_witness_Code d e.1) : ℝ) := by
    simp only [aux_gcat_band_witness_Idx, aux_gcat_band_witness_Roots, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    ring
  rw [hcardIdx]
  calc 2 * (3 * (3 : ℝ) ^ d) * (Fintype.card (Σ e : aux_gcat_band_witness_Depth cbuf D',
        aux_gcat_band_witness_Code d e.1) : ℝ)
      ≤ 2 * (3 * (3 : ℝ) ^ d) * ((1 + 3 * (3 : ℝ) ^ d) *
          Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ))) :=
        mul_le_mul_of_nonneg_left hsig (by positivity)
    _ = (6 * (3 : ℝ) ^ d * (1 + 3 * (3 : ℝ) ^ d)) * Real.exp (((d : ℝ) * Real.log 3) * (D' : ℝ)) := by
        ring

/-- Two limits in measure of eventually equal sequences along a subsequence agree almost everywhere,
one of them being an `L^p` limit. -/
theorem aux_gcat_band_witness_link
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn G : ℕ → Ω → ℝ) (Sv L : Ω → ℝ) (phi psi : ℕ → ℕ) (hpsi : StrictMono psi)
    (hphi : Tendsto phi atTop atTop) {p : ℝ≥0∞} (hp : p ≠ 0)
    (hXm : ∀ n, AEStronglyMeasurable (Xn n) μ) (hSm : AEStronglyMeasurable Sv μ)
    (hconv : Tendsto (fun kk => eLpNorm (fun ω => Xn (phi (psi kk)) ω - Sv ω) p μ) atTop (𝓝 0))
    (hG : TendstoInMeasure μ (fun n => G (phi n)) atTop L)
    (hev : ∀ᶠ N in atTop, G N = Xn N) : L =ᵐ[μ] Sv := by
  have h1 : TendstoInMeasure μ (fun kk => Xn (phi (psi kk))) atTop Sv :=
    tendstoInMeasure_of_tendsto_eLpNorm hp (fun kk => hXm _) hSm hconv
  have h2 : TendstoInMeasure μ ((fun n => G (phi n)) ∘ psi) atTop L :=
    hG.comp hpsi.tendsto_atTop
  have hev' : ∀ᶠ kk in atTop, G (phi (psi kk)) = Xn (phi (psi kk)) :=
    (hphi.comp hpsi.tendsto_atTop).eventually hev
  have h3 : TendstoInMeasure μ (fun kk => Xn (phi (psi kk))) atTop L :=
    h2.congr' (hev'.mono fun kk hk => by simp only [Function.comp_apply]; rw [hk])
      Filter.EventuallyEq.rfl
  exact tendstoInMeasure_ae_unique h3 h1

/-- The catalogue prefix `gcat_prefix` is the window sum of the guarded scores once the cutoff is deep enough. -/
theorem aux_gcat_band_witness_gcat_prefix_eq {d : ℕ}
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal) (tag : Bool) (gH cbuf k : ℕ)
    (z : SpatialCoordinates d) (U : aux_gcat_band_witness_Roots d) (D : ℕ)
    (code : aux_gcat_band_witness_Code d D) (N : ℕ)
    (hN : gcat_rootLevel gH k U + (D : ℤ) ≤ (N : ℤ)) :
    gcat_prefix gH cbuf k z (if tag then (fun N m w om => (Draw N m w om).toReal) else Z) N U D code =
      fun ω => ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
        aux_gcat_band_witness_gscore Z Draw tag N j (gcat_obsCentre gH k z U D code) ω := by
  funext ω
  unfold gcat_prefix
  rw [if_pos hN]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold aux_gcat_band_witness_gscore
  cases tag <;> simp

/-- Scale index of the `j`-th term of the window of an index. -/
def aux_gcat_band_witness_sIdx {d : ℕ} (gH cbuf k : ℕ) (D' : ℕ)
    (i : aux_gcat_band_witness_Idx d cbuf D') (j : ℕ) : ℤ :=
  gcat_rootLevel gH k i.2.1 - (cbuf : ℤ) + (j : ℤ)

/-- Observation centre of an index. -/
def aux_gcat_band_witness_cIdx {d : ℕ} (gH cbuf k : ℕ) (z : SpatialCoordinates d) (D' : ℕ)
    (i : aux_gcat_band_witness_Idx d cbuf D') : SpatialCoordinates d :=
  gcat_obsCentre gH k z i.2.1 i.2.2.1.1 i.2.2.2

/-- The limit terms of the prefix family. -/
def aux_gcat_band_witness_Yarr {d : ℕ} (V : aux_gcat_band_witness_Pos d → ℤ → Bool → BilateralField d → ℝ)
    (gH cbuf k : ℕ) (D' : ℕ) (i : aux_gcat_band_witness_Idx d cbuf D') (j : ℕ) :
    BilateralField d → ℝ :=
  V (aux_gcat_band_witness_posOf i) (aux_gcat_band_witness_sIdx gH cbuf k D' i j) i.1

/-- The finite-cutoff terms of the prefix family along the extracted cutoff sequence. -/
def aux_gcat_band_witness_Xarr {d : ℕ}
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal) (phi psi : ℕ → ℕ)
    (gH cbuf k : ℕ) (z : SpatialCoordinates d) (D' : ℕ) (i : aux_gcat_band_witness_Idx d cbuf D')
    (j : ℕ) (kk : ℕ) : BilateralField d → ℝ :=
  aux_gcat_band_witness_gscore Z Draw i.1 (phi (psi kk)) (aux_gcat_band_witness_sIdx gH cbuf k D' i j)
    (aux_gcat_band_witness_cIdx gH cbuf k z D' i)

/-- Geometry of the scale indices. -/
theorem aux_gcat_band_witness_sIdx_bounds {d : ℕ} (gH cbuf k : ℕ) (D' : ℕ)
    (i : aux_gcat_band_witness_Idx d cbuf D') (j : ℕ) (hj : j < D') :
    (k : ℤ) - ((gH + cbuf + 1 : ℕ) : ℤ) ≤ aux_gcat_band_witness_sIdx gH cbuf k D' i j ∧
      aux_gcat_band_witness_sIdx gH cbuf k D' i j ≤ (k : ℤ) + ((gH + cbuf + 1 : ℕ) : ℤ) + (D' : ℤ) := by
  unfold aux_gcat_band_witness_sIdx gcat_rootLevel
  have hfac : ∀ e : Fin 3, gcat_factor gH e = 0 ∨ gcat_factor gH e = 1 ∨ gcat_factor gH e = gH := by
    intro e
    unfold gcat_factor
    fin_cases e <;> simp
  have hf : (gcat_factor gH i.2.1.1 : ℤ) ≤ (gH : ℤ) + 1 := by
    rcases hfac i.2.1.1 with h | h | h <;> rw [h] <;> push_cast <;> omega
  have hf0 : (0 : ℤ) ≤ (gcat_factor gH i.2.1.1 : ℤ) := Int.natCast_nonneg _
  push_cast
  constructor <;> omega

/-- The array hypotheses of the prefix cover, from the limit bank and the two `lem_band` banks. -/
theorem aux_gcat_band_witness_prefix_arrays
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hM1 : M.delta ≤ 1) (p : ℝ)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal) (gH cbuf k : ℕ) (z : SpatialCoordinates d)
    (phi psi : ℕ → ℕ) (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (V : aux_gcat_band_witness_Pos d → ℤ → Bool → BilateralField d → ℝ)
    (hV : ∀ (pos : aux_gcat_band_witness_Pos d) (j : ℤ) (tag : Bool),
      MemLp (V pos j tag) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hg : ∀ (N : ℕ) (pos : aux_gcat_band_witness_Pos d) (j : ℤ) (tag : Bool),
      MemLp (aux_gcat_band_witness_gscore Z Draw tag N j
        (gcat_obsCentre gH k z pos.1 pos.2.1 pos.2.2)) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hconv : ∀ (pos : aux_gcat_band_witness_Pos d) (j : ℤ) (tag : Bool),
      Tendsto (fun kk => eLpNorm (fun ω =>
        aux_gcat_band_witness_gscore Z Draw tag (phi (psi kk)) j
          (gcat_obsCentre gH k z pos.1 pos.2.1 pos.2.2) ω - V pos j tag ω) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure) atTop (𝓝 0))
    (aZ cZ aD cD CpZ CpD : ℝ) (wZ wD : ℕ) (a c Cp' : ℝ) (Cband : ℕ)
    (haZ : a ≤ aZ) (haD : a ≤ aD) (hcZ : c ≤ cZ) (hcD : c ≤ cD) (hCZ : CpZ ≤ Cp') (hCD : CpD ≤ Cp')
    (hCZ0 : 0 ≤ CpZ) (hCD0 : 0 ≤ CpD) (hwZ : wZ ≤ Cband) (hwD : wD ≤ Cband)
    (hZbank : ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) → ∀ h : ℕ, 1 ≤ h →
      ∃ Yn : BilateralField d → ℝ,
        AEStronglyMeasurable[aux_gcat_band_witness_lbWindow d n wZ h] Yn (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega => Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega - Yn omega)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (CpZ * M.delta ^ cZ * (3 : ℝ) ^ (-(aZ * (h : ℝ)))))
    (hDbank : ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) → ∀ h : ℕ, 1 ≤ h →
      ∃ Yn : BilateralField d → ℝ,
        AEStronglyMeasurable[aux_gcat_band_witness_lbWindow d n wD h] Yn (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega => (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal - Yn omega)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (CpD * M.delta ^ cD * (3 : ℝ) ^ (-(aD * (h : ℝ))))) :
    (∀ (D' : ℕ) (i : aux_gcat_band_witness_Idx d cbuf D') (j : ℕ),
      MemLp (aux_gcat_band_witness_Yarr V gH cbuf k D' i j) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure) ∧
    (∀ (D' : ℕ) (i : aux_gcat_band_witness_Idx d cbuf D') (j kk : ℕ),
      MemLp (aux_gcat_band_witness_Xarr Z Draw phi psi gH cbuf k z D' i j kk) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure) ∧
    (∀ (D' : ℕ) (i : aux_gcat_band_witness_Idx d cbuf D') (j : ℕ),
      Tendsto (fun kk => eLpNorm (aux_gcat_band_witness_Xarr Z Draw phi psi gH cbuf k z D' i j kk -
        aux_gcat_band_witness_Yarr V gH cbuf k D' i j) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure) atTop (𝓝 0)) ∧
    (∀ (D' : ℕ) (i : aux_gcat_band_witness_Idx d cbuf D') (j H : ℕ), 1 ≤ H →
      ∀ᶠ kk in atTop, ∃ Yn : BilateralField d → ℝ,
        AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d
          (aux_gcat_band_witness_sIdx gH cbuf k D' i j - ((Cband * (H + 1) : ℕ) : ℤ))
          (aux_gcat_band_witness_sIdx gH cbuf k D' i j + ((Cband * (H + 1) : ℕ) : ℤ))] Yn
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => aux_gcat_band_witness_Xarr Z Draw phi psi gH cbuf k z D' i j kk om - Yn om)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (2 * Cp' * M.delta ^ c / 2 * (3 : ℝ) ^ (-(a * (H : ℝ))))) := by
  refine ⟨fun D' i j => ?_, fun D' i j kk => ?_, fun D' i j => ?_, ?_⟩
  · exact hV (aux_gcat_band_witness_posOf i) (aux_gcat_band_witness_sIdx gH cbuf k D' i j) i.1
  · exact hg (phi (psi kk)) (aux_gcat_band_witness_posOf i) (aux_gcat_band_witness_sIdx gH cbuf k D' i j) i.1
  · exact hconv (aux_gcat_band_witness_posOf i) (aux_gcat_band_witness_sIdx gH cbuf k D' i j) i.1
  intro D' i j H hH
  have hphipsi : Tendsto (fun kk => phi (psi kk)) atTop atTop :=
    hphi.tendsto_atTop.comp hpsi.tendsto_atTop
  have := aux_gcat_band_witness_prefix_hband d M hM1 p Z Draw aZ cZ aD cD CpZ CpD wZ wD a c Cp' Cband
    haZ haD hcZ hcD hCZ hCD hCZ0 hCD0 hwZ hwD hZbank hDbank
    (aux_gcat_band_witness_sIdx gH cbuf k D' i j) (aux_gcat_band_witness_cIdx gH cbuf k z D' i) i.1
    (fun kk => phi (psi kk)) hphipsi H hH
  filter_upwards [this] with kk hkk
  obtain ⟨Yn, hYn1, hYn2⟩ := hkk
  refine ⟨Yn, hYn1, ?_⟩
  refine hYn2.trans (le_of_eq ?_)
  congr 1
  ring

/-- The exceedance tail of the limit window sums, in the form required by the prefix cover. -/
theorem aux_gcat_band_witness_prefix_tailP
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal) (gH cbuf k : ℕ) (z : SpatialCoordinates d)
    (k0 : ℕ) (hk0 : 1 ≤ k0) (lam' Atail : ℝ) (hlam' : 0 < lam') (hAtail : 0 < Atail)
    (phi : ℕ → ℕ)
    (V : aux_gcat_band_witness_Pos d → ℤ → Bool → BilateralField d → ℝ)
    (hpass : ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D)
        (tag : Bool) (A a a' : ℝ), 0 < A → a < a' →
      (∀ n, (chaosSampleLaw M).toMeasure {ω | a <
        ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
          aux_gcat_band_witness_gscore Z Draw tag (phi n) j (gcat_obsCentre gH k z U D code) ω} ≤
        ENNReal.ofReal (Real.exp (-(A * (D : ℝ))))) →
      (chaosSampleLaw M).toMeasure {ω | a' <
        ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
          V ⟨U, ⟨D, code⟩⟩ j tag ω} ≤ ENNReal.ofReal (Real.exp (-(A * (D : ℝ)))))
    (hfin : ∀ (N : ℕ) (U : aux_gcat_band_witness_Roots d) (D : ℕ), 1 ≤ D →
      ∀ (code : aux_gcat_band_witness_Code d D) (tag : Bool),
      (chaosSampleLaw M).toMeasure {om | lam' * (D : ℝ) / 4 <
        ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
          aux_gcat_band_witness_gscore Z Draw tag N j (gcat_obsCentre gH k z U D code) om} ≤
        ENNReal.ofReal (2 * Real.exp (-((Atail + Real.log 2) * (D : ℝ))))) :
    ∀ D', k0 + cbuf + 1 ≤ D' → ∀ i : aux_gcat_band_witness_Idx d cbuf D',
      (chaosSampleLaw M).toMeasure {om | lam' * (D' : ℝ) / 4 <
        ∑ j ∈ Finset.range D', aux_gcat_band_witness_Yarr V gH cbuf k D' i j om} ≤
      ENNReal.ofReal (Real.exp (Atail * ((cbuf : ℝ) + 1)) * Real.exp (-(Atail * (D' : ℝ)))) := by
  intro D' hD' i
  obtain ⟨tag, U, ⟨D0, hD0⟩, code⟩ := i
  subst hD0
  have hD01 : 1 ≤ D0 := by omega
  have hsum : ∀ om, ∑ j ∈ Finset.range (D0 + cbuf + 1),
      aux_gcat_band_witness_Yarr V gH cbuf k (D0 + cbuf + 1) (tag, U, ⟨⟨D0, rfl⟩, code⟩) j om =
      ∑ t ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D0 : ℤ)),
        V ⟨U, ⟨D0, code⟩⟩ t tag om := by
    intro om
    exact aux_gcat_band_witness_sum_range_eq_sum_Icc (fun t => V ⟨U, ⟨D0, code⟩⟩ t tag om)
      (gcat_rootLevel gH k U) D0 cbuf
  simp only [hsum]
  have hD0r : (0 : ℝ) < (D0 : ℝ) := by exact_mod_cast hD01
  have hcb : (0 : ℝ) < (cbuf : ℝ) + 1 := by positivity
  have hlt : lam' * (D0 : ℝ) / 4 < lam' * (((D0 + cbuf + 1 : ℕ) : ℝ)) / 4 := by
    push_cast
    nlinarith
  have hfin' : ∀ n, (chaosSampleLaw M).toMeasure {ω | lam' * (D0 : ℝ) / 4 <
      ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D0 : ℤ)),
        aux_gcat_band_witness_gscore Z Draw tag (phi n) j (gcat_obsCentre gH k z U D0 code) ω} ≤
      ENNReal.ofReal (Real.exp (-(Atail * (D0 : ℝ)))) := by
    intro n
    refine (hfin (phi n) U D0 hD01 code tag).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    have hD0ge : (1 : ℝ) ≤ (D0 : ℝ) := by exact_mod_cast hD01
    calc 2 * Real.exp (-((Atail + Real.log 2) * (D0 : ℝ)))
        = Real.exp (Real.log 2) * Real.exp (-((Atail + Real.log 2) * (D0 : ℝ))) := by rw [← h2]
      _ = Real.exp (Real.log 2 - (Atail + Real.log 2) * (D0 : ℝ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(Atail * (D0 : ℝ))) := by
          apply Real.exp_le_exp.mpr
          have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          nlinarith
  have hres := hpass U D0 code tag Atail _ _ hAtail hlt hfin'
  refine hres.trans (le_of_eq ?_)
  congr 1
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Almost-sure passage from a failed catalogue prefix inequality to the cover of the abstract prefix family. -/
theorem aux_gcat_band_witness_prefix_finish
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (gH cbuf k k0 : ℕ) (hk0 : 1 ≤ k0) (lambdaLim lam' : ℝ) (hlam : 0 < lambdaLim)
    (hlam' : lam' = lambdaLim * (k0 : ℝ) / ((k0 + cbuf + 1 : ℕ) : ℝ))
    (V : aux_gcat_band_witness_Pos d → ℤ → Bool → BilateralField d → ℝ)
    (ZLim DLim : aux_gcat_band_witness_Roots d → ∀ D : ℕ, aux_gcat_band_witness_Code d D →
      BilateralField d → ℝ)
    (Sigma : Set (BilateralField d)) (hSigmeas : MeasurableSet Sigma) (hSigP : P Sigma = 1)
    (Wc : ℕ+ → Set (BilateralField d))
    (hWcov : Sigma ∩ {om | ∃ D', k0 + cbuf + 1 ≤ D' ∧ ∃ i : aux_gcat_band_witness_Idx d cbuf D',
      lam' * (D' : ℝ) ≤ ∑ j ∈ Finset.range D', aux_gcat_band_witness_Yarr V gH cbuf k D' i j om} ⊆
      ⋃ h : ℕ+, Wc h)
    (hlinkZ : ∀ᵐ ω ∂P, ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D),
      ZLim U D code ω = ∑ t ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
        V ⟨U, ⟨D, code⟩⟩ t false ω)
    (hlinkD : ∀ᵐ ω ∂P, ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D),
      DLim U D code ω = ∑ t ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
        V ⟨U, ⟨D, code⟩⟩ t true ω) :
    ∀ᵐ omega ∂P,
      (¬ ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ), k0 ≤ D → ∀ code : aux_gcat_band_witness_Code d D,
          ZLim U D code omega < lambdaLim * (D : ℝ) ∧ DLim U D code omega < lambdaLim * (D : ℝ)) →
      omega ∈ ⋃ h : ℕ+, Wc h := by
  have hSig : ∀ᵐ ω ∂P, ω ∈ Sigma := by
    have h0 : P Sigmaᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hSigmeas]; exact hSigP
    exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono (fun ω h => by simpa using h)
  filter_upwards [hSig, hlinkZ, hlinkD] with ω hωS hZ hD hnot
  push_neg at hnot
  obtain ⟨U, D, hkD, code, hbad⟩ := hnot
  have hk0r : (0 : ℝ) < (k0 : ℝ) := by exact_mod_cast hk0
  have hkD' : (k0 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hkD
  have hkpos : (0 : ℝ) < ((k0 + cbuf + 1 : ℕ) : ℝ) := by positivity
  -- the threshold comparison `lam' * D' ≤ lambdaLim * D`
  have hcmp : lam' * (((D + cbuf + 1 : ℕ)) : ℝ) ≤ lambdaLim * (D : ℝ) := by
    rw [hlam']
    push_cast at hkpos ⊢
    rw [div_mul_eq_mul_div, div_le_iff₀ hkpos]
    have : (k0 : ℝ) * ((D : ℝ) + (cbuf : ℝ) + 1) ≤ (D : ℝ) * ((k0 : ℝ) + (cbuf : ℝ) + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) cbuf]
    nlinarith
  have hD' : k0 + cbuf + 1 ≤ D + cbuf + 1 := by omega
  by_cases hZbad : lambdaLim * (D : ℝ) ≤ ZLim U D code ω
  · refine hWcov ⟨hωS, D + cbuf + 1, hD', (false, U, ⟨⟨D, rfl⟩, code⟩), ?_⟩
    have hsum : ∑ j ∈ Finset.range (D + cbuf + 1), aux_gcat_band_witness_Yarr V gH cbuf k (D + cbuf + 1)
        (false, U, ⟨⟨D, rfl⟩, code⟩) j ω =
        ∑ t ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
          V ⟨U, ⟨D, code⟩⟩ t false ω :=
      aux_gcat_band_witness_sum_range_eq_sum_Icc (fun t => V ⟨U, ⟨D, code⟩⟩ t false ω)
        (gcat_rootLevel gH k U) D cbuf
    show lam' * ((D + cbuf + 1 : ℕ) : ℝ) ≤ _
    rw [hsum, ← hZ U D code]
    exact hcmp.trans hZbad
  · have hDbad : lambdaLim * (D : ℝ) ≤ DLim U D code ω := hbad (lt_of_not_ge hZbad)
    refine hWcov ⟨hωS, D + cbuf + 1, hD', (true, U, ⟨⟨D, rfl⟩, code⟩), ?_⟩
    have hsum : ∑ j ∈ Finset.range (D + cbuf + 1), aux_gcat_band_witness_Yarr V gH cbuf k (D + cbuf + 1)
        (true, U, ⟨⟨D, rfl⟩, code⟩) j ω =
        ∑ t ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
          V ⟨U, ⟨D, code⟩⟩ t true ω :=
      aux_gcat_band_witness_sum_range_eq_sum_Icc (fun t => V ⟨U, ⟨D, code⟩⟩ t true ω)
        (gcat_rootLevel gH k U) D cbuf
    show lam' * ((D + cbuf + 1 : ℕ) : ℝ) ≤ _
    rw [hsum, ← hD U D code]
    exact hcmp.trans hDbad

/-- Almost-sure identification of the catalogue limit arrays with the window sums of the limit scores. -/
theorem aux_gcat_band_witness_prefix_links
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p : ℝ) (hp : 1 ≤ p)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal) (gH cbuf k : ℕ) (z : SpatialCoordinates d)
    (phi psi : ℕ → ℕ) (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (V : aux_gcat_band_witness_Pos d → ℤ → Bool → BilateralField d → ℝ)
    (hV : ∀ (pos : aux_gcat_band_witness_Pos d) (j : ℤ) (tag : Bool),
      MemLp (V pos j tag) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hg : ∀ (N : ℕ) (pos : aux_gcat_band_witness_Pos d) (j : ℤ) (tag : Bool),
      MemLp (aux_gcat_band_witness_gscore Z Draw tag N j
        (gcat_obsCentre gH k z pos.1 pos.2.1 pos.2.2)) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hWconv : ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D)
        (tag : Bool),
      Tendsto (fun kk => eLpNorm (fun ω =>
        ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
          aux_gcat_band_witness_gscore Z Draw tag (phi (psi kk)) j
            (gcat_obsCentre gH k z U D code) ω -
        ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
          V ⟨U, ⟨D, code⟩⟩ j tag ω) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0))
    (ZLim DLim : aux_gcat_band_witness_Roots d → ∀ D : ℕ, aux_gcat_band_witness_Code d D →
      BilateralField d → ℝ)
    (hZ : ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n omega => gcat_prefix gH cbuf k z Z (phi n) U D code omega) atTop (ZLim U D code))
    (hD : ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n omega => gcat_prefix gH cbuf k z (fun N m w om => (Draw N m w om).toReal) (phi n)
          U D code omega) atTop (DLim U D code)) :
    (∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ)
        (code : aux_gcat_band_witness_Code d D),
      ZLim U D code ω = ∑ t ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ))
        (gcat_rootLevel gH k U + (D : ℤ)), V ⟨U, ⟨D, code⟩⟩ t false ω) ∧
    (∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ)
        (code : aux_gcat_band_witness_Code d D),
      DLim U D code ω = ∑ t ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ))
        (gcat_rootLevel gH k U + (D : ℤ)), V ⟨U, ⟨D, code⟩⟩ t true ω) := by
  classical
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hphiT : Tendsto phi atTop atTop := hphi.tendsto_atTop
  have hsumMeas : ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D)
      (tag : Bool) (N : ℕ), AEStronglyMeasurable (fun ω =>
        ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
          aux_gcat_band_witness_gscore Z Draw tag N j (gcat_obsCentre gH k z U D code) ω)
        (chaosSampleLaw M).toMeasure := by
    intro U D code tag N
    have hsum := Finset.aestronglyMeasurable_sum
      (Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)))
      (fun jj _ => (hg N ⟨U, ⟨D, code⟩⟩ jj tag).aestronglyMeasurable)
    rwa [Finset.sum_fn] at hsum
  have hsumV : ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D)
      (tag : Bool), AEStronglyMeasurable (fun ω =>
        ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
          V ⟨U, ⟨D, code⟩⟩ j tag ω) (chaosSampleLaw M).toMeasure := by
    intro U D code tag
    have hsum := Finset.aestronglyMeasurable_sum
      (Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)))
      (fun jj _ => (hV ⟨U, ⟨D, code⟩⟩ jj tag).aestronglyMeasurable)
    rwa [Finset.sum_fn] at hsum
  constructor
  · refine ae_all_iff.mpr (fun U => ae_all_iff.mpr (fun D => ae_all_iff.mpr (fun code => ?_)))
    have hL := aux_gcat_band_witness_link (chaosSampleLaw M).toMeasure
      (fun N ω => ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
        aux_gcat_band_witness_gscore Z Draw false N j (gcat_obsCentre gH k z U D code) ω)
      (fun N => gcat_prefix gH cbuf k z Z N U D code)
      (fun ω => ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
        V ⟨U, ⟨D, code⟩⟩ j false ω) (ZLim U D code) phi psi hpsi hphiT hp0
      (fun N => hsumMeas U D code false N) (hsumV U D code false) (hWconv U D code false)
      (hZ U D code) ?_
    · exact hL
    · filter_upwards [eventually_ge_atTop (gcat_rootLevel gH k U + (D : ℤ)).toNat] with N hN
      have hNge : gcat_rootLevel gH k U + (D : ℤ) ≤ (N : ℤ) :=
        le_trans (Int.self_le_toNat _) (by exact_mod_cast hN)
      have := aux_gcat_band_witness_gcat_prefix_eq Z Draw false gH cbuf k z U D code N hNge
      simpa using this
  · refine ae_all_iff.mpr (fun U => ae_all_iff.mpr (fun D => ae_all_iff.mpr (fun code => ?_)))
    have hL := aux_gcat_band_witness_link (chaosSampleLaw M).toMeasure
      (fun N ω => ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
        aux_gcat_band_witness_gscore Z Draw true N j (gcat_obsCentre gH k z U D code) ω)
      (fun N => gcat_prefix gH cbuf k z (fun N m w om => (Draw N m w om).toReal) N U D code)
      (fun ω => ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
        V ⟨U, ⟨D, code⟩⟩ j true ω) (DLim U D code) phi psi hpsi hphiT hp0
      (fun N => hsumMeas U D code true N) (hsumV U D code true) (hWconv U D code true)
      (hD U D code) ?_
    · exact hL
    · filter_upwards [eventually_ge_atTop (gcat_rootLevel gH k U + (D : ℤ)).toNat] with N hN
      have hNge : gcat_rootLevel gH k U + (D : ℤ) ≤ (N : ℤ) :=
        le_trans (Int.self_le_toNat _) (by exact_mod_cast hN)
      have := aux_gcat_band_witness_gcat_prefix_eq Z Draw true gH cbuf k z U D code N hNge
      simpa using this

/-- Interval-witness cover of the failure of the prefix conditions of a catalogue cell. -/
theorem gcat_band_witness_prefix
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (Dbase : Paper.sum_errors_baseline_input d)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (gH cbuf k0 : ℕ) (hk0 : 1 ≤ k0)
    (lambdaLim : ℝ) (hlam : 0 < lambdaLim) (A : ℝ) (hA : 0 < A) :
    ∃ deltaW : ℝ, 0 < deltaW ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaW →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          primitive_scores d M s eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
      ∀ (k : ℕ) (z : SpatialCoordinates d) (phi : ℕ → ℕ), StrictMono phi →
      ∀ (ZLim DLim : aux_gcat_band_witness_Roots d → ∀ D : ℕ, aux_gcat_band_witness_Code d D →
        BilateralField d → ℝ),
        (∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => gcat_prefix gH cbuf k z Z (phi n) U D code omega) atTop (ZLim U D code)) →
        (∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ) (code : aux_gcat_band_witness_Code d D),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => gcat_prefix gH cbuf k z (fun N m w om => (Draw N m w om).toReal) (phi n)
              U D code omega) atTop (DLim U D code)) →
        ∃ Wc : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d ((k : ℤ) - (h : ℤ))
            ((k : ℤ) + 2 * (h : ℤ))] (Wc h)) ∧
          (∀ h : ℕ+, (chaosSampleLaw M).toMeasure (Wc h) ≤
            ENNReal.ofReal (Real.exp (-(A * ((h : ℕ) : ℝ))))) ∧
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            (¬ ∀ (U : aux_gcat_band_witness_Roots d) (D : ℕ), k0 ≤ D →
              ∀ code : aux_gcat_band_witness_Code d D,
                ZLim U D code omega < lambdaLim * (D : ℝ) ∧ DLim U D code omega < lambdaLim * (D : ℝ)) →
            omega ∈ ⋃ h : ℕ+, Wc h := by
  classical
  -- (1) the two `lem_band` banks: common constants
  obtain ⟨aZ, cZ, wZ, haZ, hcZ, hwZ, hZb⟩ :=
    aux_gcat_band_witness_bank_Z d hd I Pc Xc W Sf Dd Cresp hCresp Dbase s sigma eps hs hsigma heps
  obtain ⟨aD, cD, wD, haD, hcD, hwD, hDb⟩ :=
    aux_gcat_band_witness_bank_D d hd I Pc Xc W Sf Dd Cresp hCresp Dbase s sigma eps hs hsigma heps
  have hCband0 : 0 < max wZ wD := lt_of_lt_of_le hwZ (le_max_left _ _)
  obtain ⟨Cband, hCbandDef⟩ : ∃ Cband : ℕ, Cband = max wZ wD := ⟨_, rfl⟩
  have hCband : 0 < Cband := by rw [hCbandDef]; exact hCband0
  have hwZC : wZ ≤ Cband := by rw [hCbandDef]; exact le_max_left _ _
  have hwDC : wD ≤ Cband := by rw [hCbandDef]; exact le_max_right _ _
  obtain ⟨a, haDef⟩ : ∃ a : ℝ, a = min aZ aD := ⟨_, rfl⟩
  obtain ⟨c, hcDef⟩ : ∃ c : ℝ, c = min cZ cD := ⟨_, rfl⟩
  have ha : 0 < a := by rw [haDef]; exact lt_min haZ haD
  have hc : 0 < c := by rw [hcDef]; exact lt_min hcZ hcD
  have haaZ : a ≤ aZ := by rw [haDef]; exact min_le_left _ _
  have haaD : a ≤ aD := by rw [haDef]; exact min_le_right _ _
  have hccZ : c ≤ cZ := by rw [hcDef]; exact min_le_left _ _
  have hccD : c ≤ cD := by rw [hcDef]; exact min_le_right _ _
  obtain ⟨v, hvDef⟩ : ∃ v : ℝ, v = (d : ℝ) * Real.log 3 := ⟨_, rfl⟩
  have hv : 0 ≤ v := by
    rw [hvDef]; exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  obtain ⟨Cgeom, hCgeomDef⟩ : ∃ Cgeom : ℝ, Cgeom = 6 * (3 : ℝ) ^ d * (1 + 3 * (3 : ℝ) ^ d) := ⟨_, rfl⟩
  have hCgeom : 1 ≤ Cgeom := by
    rw [hCgeomDef]
    have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith
  obtain ⟨c0, hc0Def⟩ : ∃ c0 : ℕ, c0 = gH + cbuf + 1 := ⟨_, rfl⟩
  obtain ⟨k0', hk0'Def⟩ : ∃ k0' : ℕ, k0' = k0 + cbuf + 1 := ⟨_, rfl⟩
  have hk0' : 1 ≤ k0' := by omega
  obtain ⟨lam', hlam'Def⟩ : ∃ lam' : ℝ, lam' = lambdaLim * (k0 : ℝ) / (k0' : ℝ) := ⟨_, rfl⟩
  have hk0r : (0 : ℝ) < (k0 : ℝ) := by exact_mod_cast hk0
  have hk0'r : (0 : ℝ) < (k0' : ℝ) := by exact_mod_cast hk0'
  have hlam' : 0 < lam' := by rw [hlam'Def]; positivity
  obtain ⟨Atail, p, hAtail, hp2, hAt1, hp1, hAk0⟩ :=
    aux_gcat_band_witness_prefix_constants Cband cbuf k0 c0 hk0 A v Cgeom a hCgeom ha
  have hp1' : (1 : ℝ) ≤ p := by linarith only [hp2]
  obtain ⟨δZ, CpZ, hδZ, hCpZ, hZbank⟩ := hZb p hp1'
  obtain ⟨δD, CpD, hδD, hCpD, hDbank⟩ := hDb p hp1'
  obtain ⟨Cp', hCp'Def⟩ : ∃ Cp' : ℝ, Cp' = max CpZ CpD := ⟨_, rfl⟩
  have hCp' : 0 < Cp' := by rw [hCp'Def]; exact lt_of_lt_of_le hCpZ (le_max_left _ _)
  have hCpZ' : CpZ ≤ Cp' := by rw [hCp'Def]; exact le_max_left _ _
  have hCpD' : CpD ≤ Cp' := by rw [hCp'Def]; exact le_max_right _ _
  obtain ⟨δL, hδL, hLB⟩ := aux_gcat_band_witness_prefix_limit_bank d hd I Pc Xc W Sf Dd Cresp hCresp
    s sigma eps hs hsigma heps p hp1'
  obtain ⟨δT, hδT, hTail⟩ := prefix_physical_tail d s eps lam' (Atail + Real.log 2) cbuf hs heps hlam'
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith only [hAtail, this])
  have hAk0' : Real.log (9 * Cgeom * Real.exp (Atail * ((cbuf : ℝ) + 1))) + A * ((Cband : ℝ) + (c0 : ℝ)) ≤
      (Atail - v - A * ((Cband : ℝ) + 1)) * (k0' : ℝ) := by
    rw [hk0'Def]; exact hAk0
  obtain ⟨eta0, heta0, hcore2⟩ := gcat_band_witness_prefix_core2 d Cband c0 k0' hCband hk0' A a lam' v
    Cgeom hA ha hlam' hv hCgeom p Atail (Real.exp (Atail * ((cbuf : ℝ) + 1))) (2 * Cp') hp2
    (Real.exp_pos _) (by positivity) hAt1 hp1 hAk0'
  refine ⟨min (min (min δZ δD) (min δL δT)) (min (1 / 2) (eta0 ^ (1 / c))), ?_, ?_⟩
  · refine lt_min (lt_min (lt_min hδZ hδD) (lt_min hδL hδT)) (lt_min (by norm_num) ?_)
    exact Real.rpow_pos_of_pos heta0 _
  intro M hMd Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim k z phi hphi ZLim DLim hZ hD
  -- (2) the model
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  obtain ⟨hMa, hMb⟩ := le_min_iff.mp hMd
  obtain ⟨hMa1, hMa2⟩ := le_min_iff.mp hMa
  obtain ⟨hMZ, hMD⟩ := le_min_iff.mp hMa1
  obtain ⟨hML, hMT⟩ := le_min_iff.mp hMa2
  obtain ⟨hMhalf, hMeta⟩ := le_min_iff.mp hMb
  have hM1 : M.delta ≤ 1 := by linarith only [hMhalf]
  have hle : M.delta ^ c ≤ eta0 := by
    calc M.delta ^ c ≤ (eta0 ^ (1 / c)) ^ c := Real.rpow_le_rpow hdpos.le hMeta hc.le
      _ = eta0 := by
        rw [← Real.rpow_mul heta0.le, one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
  have hZbankM := hZbank M hMZ Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
  have hDbankM := hDbank M hMD Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
  obtain ⟨psi, hpsi, V, hVmem, hgmem, hVconv, hWconv, hVpass⟩ :=
    hLB M hML Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim gH cbuf k z phi hphi
  have hphys := hTail M hMT eta heta F Praw Rraw Draw Z rawGood hprim
  have hfin := fun N U D hD code tag =>
    aux_gcat_band_witness_prefix_tail_finite d M s eps lam' (Atail + Real.log 2) cbuf gH k z eta
      F Praw Rraw Draw Z rawGood hprim (fun N k D hD e w useD => (hphys N k D hD e w useD).1)
      N U D hD code tag
  obtain ⟨hYmem, hXmem, hYconv, hYband⟩ :=
    aux_gcat_band_witness_prefix_arrays d M hM1 p Z Draw gH cbuf k z phi psi hphi hpsi V hVmem hgmem
      hVconv aZ cZ aD cD CpZ CpD wZ wD a c Cp' Cband haaZ haaD hccZ hccD hCpZ' hCpD' hCpZ.le hCpD.le
      hwZC hwDC hZbankM hDbankM
  have htailP := aux_gcat_band_witness_prefix_tailP d M Z Draw gH cbuf k z k0 hk0 lam' Atail hlam'
    hAtail phi V hVpass hfin
  have hcard : ∀ D', (Fintype.card (aux_gcat_band_witness_Idx d cbuf D') : ℝ) ≤
      Cgeom * Real.exp (v * (D' : ℝ)) := by
    intro D'
    rw [hCgeomDef, hvDef]
    exact aux_gcat_band_witness_Idx_card d cbuf D'
  have hsb : ∀ (D' : ℕ) (i : aux_gcat_band_witness_Idx d cbuf D') (j : ℕ), j < D' →
      (k : ℤ) - (c0 : ℤ) ≤ aux_gcat_band_witness_sIdx gH cbuf k D' i j ∧
        aux_gcat_band_witness_sIdx gH cbuf k D' i j ≤ (k : ℤ) + (c0 : ℤ) + (D' : ℤ) := by
    intro D' i j hj
    rw [hc0Def]
    exact aux_gcat_band_witness_sIdx_bounds gH cbuf k D' i j hj
  have hcore := hcore2 (M.delta ^ c) (Real.rpow_pos_of_pos hdpos c) hle M (k : ℤ)
    (aux_gcat_band_witness_Idx d cbuf) hcard (aux_gcat_band_witness_sIdx gH cbuf k) hsb
    (aux_gcat_band_witness_Yarr V gH cbuf k)
    (aux_gcat_band_witness_Xarr Z Draw phi psi gH cbuf k z) hYmem hXmem hYconv hYband
    (by rw [hk0'Def]; exact htailP)
  obtain ⟨Sigma, hSigmeas, hSigP, Wc, hWmeas, hWprob, hWcov⟩ := hcore
  obtain ⟨hlinkZ, hlinkD⟩ := aux_gcat_band_witness_prefix_links d M p hp1' Z Draw gH cbuf k z phi psi hphi
    hpsi V hVmem hgmem hWconv ZLim DLim hZ hD
  refine ⟨Wc, hWmeas, hWprob, ?_⟩
  refine aux_gcat_band_witness_prefix_finish d (chaosSampleLaw M).toMeasure gH cbuf k k0 hk0 lambdaLim
    lam' hlam (by rw [hlam'Def, hk0'Def]) V ZLim DLim Sigma hSigmeas hSigP Wc ?_ hlinkZ hlinkD
  rw [hk0'Def] at hWcov
  exact hWcov

end Paper
