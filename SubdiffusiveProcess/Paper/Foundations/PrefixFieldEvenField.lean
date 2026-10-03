module

public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldFieldLp
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldEvenBank
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldEvenSeries

@[expose] public section

noncomputable section

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper

theorem prefix_eta_bank_raw_window_eLpNorm_even {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j i : ℕ) (hi : i ∈ Finset.Icc (m - j) (m + j))
    (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d =>
      aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega))
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) *
        ENNReal.ofReal (2 * ((q : ℝ) + 1 + prefix_log_card d j)) := by
  have hσ := aux_psf_sigma_pos M
  have hpoint : ∀ omega : BilateralField d,
      ‖aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega)‖ ≤
      aux_psf_sigma M *
        ‖aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
          aux_psf_sigma M‖ := by
    intro omega
    have hb := prefix_bank_maxObs_nonneg i (m + 1 + j) z (eta N omega)
    have hdiv : 0 ≤ aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
        aux_psf_sigma M := div_nonneg hb hσ.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb,
      abs_of_nonneg hdiv]
    rw [mul_div_cancel₀ _ hσ.ne']
  calc
    eLpNorm (fun omega : BilateralField d =>
      aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega))
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) *
        eLpNorm (fun omega : BilateralField d =>
          aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
            aux_psf_sigma M) ((2 * q : ℕ) : ENNReal)
            (chaosSampleLaw M).toMeasure :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (((prefix_bank_maxObs_measurable i (m + 1 + j) z).comp_aemeasurable
          (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable)
        (Filter.Eventually.of_forall hpoint) _
    _ ≤ ENNReal.ofReal (aux_psf_sigma M) *
      ENNReal.ofReal (2 * ((q : ℝ) + 1 + prefix_log_card d j)) := by
        gcongr
        exact prefix_eta_bank_raw_window_eLpNorm_even_linear
          M eta hEta N m j i hi z q hq


theorem prefix_eta_bank_raw_window_eLpNorm_even_sum {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d =>
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega))
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ((Finset.Icc (m - j) (m + j)).card : ENNReal) *
        (ENNReal.ofReal (aux_psf_sigma M) *
          ENNReal.ofReal (2 * ((q : ℝ) + 1 + prefix_log_card d j))) := by
  let p : ENNReal := ((2 * q : ℕ) : ENNReal)
  let f : ℕ → BilateralField d → ℝ := fun i omega =>
    aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega)
  have hmeas : ∀ i ∈ Finset.Icc (m - j) (m + j),
      AEStronglyMeasurable (f i) (chaosSampleLaw M).toMeasure := by
    intro i _
    exact ((prefix_bank_maxObs_measurable i (m + 1 + j) z).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
  have hp : 1 ≤ p := by
    dsimp [p]
    exact_mod_cast (show 1 ≤ 2 * q by omega)
  have hsum := eLpNorm_sum_le (μ := (chaosSampleLaw M).toMeasure) (f := f)
    (s := Finset.Icc (m - j) (m + j)) hp
  have hfun : (∑ i ∈ Finset.Icc (m - j) (m + j), f i) =
      (fun omega => ∑ i ∈ Finset.Icc (m - j) (m + j), f i omega) := by
    funext omega
    simp only [Finset.sum_apply]
  rw [hfun] at hsum
  calc
    eLpNorm (fun omega : BilateralField d =>
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega))
      p (chaosSampleLaw M).toMeasure ≤
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        eLpNorm (f i) p (chaosSampleLaw M).toMeasure := hsum
    _ ≤ ∑ _i ∈ Finset.Icc (m - j) (m + j),
      ENNReal.ofReal (aux_psf_sigma M) *
        ENNReal.ofReal (2 * ((q : ℝ) + 1 + prefix_log_card d j)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact prefix_eta_bank_raw_window_eLpNorm_even
            M eta hEta N m j i hi z q hq
    _ = ((Finset.Icc (m - j) (m + j)).card : ENNReal) *
        (ENNReal.ofReal (aux_psf_sigma M) *
          ENNReal.ofReal (2 * ((q : ℝ) + 1 + prefix_log_card d j))) := by
            rw [Finset.sum_const, nsmul_eq_mul]


theorem prefix_eta_real_Fmaj_eLpNorm_even {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d =>
      prefix_real_Fmaj s m z j (eta N omega)) ((2 * q : ℕ) : ENNReal)
      (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (prefix_even_series_bound M s q j) := by
  let c : ℝ := (3 : ℝ) ^ (-(s * (j : ℝ) / 8))
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  let g : BilateralField d → ℝ := fun omega =>
    ∑ i ∈ Finset.Icc (m - j) (m + j),
      aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega)
  have hpoint : ∀ omega : BilateralField d,
      ‖prefix_real_Fmaj s m z j (eta N omega)‖ ≤ c * ‖g omega‖ := by
    intro omega
    unfold prefix_real_Fmaj g c
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg (by norm_num) _)]
  have hcard : ((Finset.Icc (m - j) (m + j)).card : ENNReal) ≤
      ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ)) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    have hc : (Finset.Icc (m - j) (m + j)).card ≤ 2 * j + 1 := by
      rw [Nat.card_Icc]
      omega
    exact Nat.cast_le.mpr hc
  calc
    eLpNorm (fun omega : BilateralField d =>
      prefix_real_Fmaj s m z j (eta N omega)) ((2 * q : ℕ) : ENNReal)
      (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal c * eLpNorm g ((2 * q : ℕ) : ENNReal)
          (chaosSampleLaw M).toMeasure :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (((prefix_real_Fmaj_measurable s m z j).comp_aemeasurable
          (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable)
        (Filter.Eventually.of_forall hpoint) _
    _ ≤ ENNReal.ofReal c *
        (((Finset.Icc (m - j) (m + j)).card : ENNReal) *
          (ENNReal.ofReal (aux_psf_sigma M) *
            ENNReal.ofReal (2 * ((q : ℝ) + 1 + prefix_log_card d j)))) := by
          gcongr
          exact prefix_eta_bank_raw_window_eLpNorm_even_sum
            M eta hEta N m j z q hq
    _ ≤ ENNReal.ofReal c *
        (ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ)) *
          (ENNReal.ofReal (aux_psf_sigma M) *
            ENNReal.ofReal (2 * ((q : ℝ) + 1 + prefix_log_card d j)))) := by gcongr
    _ = ENNReal.ofReal (prefix_even_series_bound M s q j) := by
      dsimp [prefix_even_series_bound, c]
      rw [← ENNReal.ofReal_mul (aux_psf_sigma_pos M).le,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      congr 1
      ring


theorem prefix_eta_real_Fmaj_tsum_eLpNorm_even {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d =>
      ∑' j : ℕ, prefix_real_Fmaj s m z j (eta N omega))
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
        ∑' j : ℕ, ENNReal.ofReal (prefix_even_series_bound M s q j) := by
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let f : ℕ → BilateralField d → ℝ := fun j omega =>
    prefix_real_Fmaj s m z j (eta N omega)
  have hf : ∀ j, AEStronglyMeasurable (f j) μ := by
    intro j
    exact ((prefix_real_Fmaj_measurable s m z j).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
  have hpush : ∀ᵐ potential ∂Measure.map (eta N) μ,
      (∑' j : ℕ, prefix_bank_Fmaj s m z j potential) ≠ ⊤ := by
    dsimp [μ]
    rw [prefix_eta_law M eta hEta N]
    exact prefix_bank_Fmaj_tsum_ae M s hs m z
  have htail := ae_of_ae_map (prefix_eta_aemeasurable M eta hEta N) hpush
  have hpoint : ∀ᵐ omega ∂μ, Summable (fun j => f j omega) := by
    filter_upwards [htail] with omega hω
    have hsum := ENNReal.summable_toReal hω
    simpa only [f, prefix_bank_Fmaj_toReal_eq] using hsum
  have hp : (1 : ENNReal) ≤ ((2 * q : ℕ) : ENNReal) := by
    exact_mod_cast (show 1 ≤ 2 * q by omega)
  have hbound : ∀ n : ℕ,
      eLpNorm (fun omega => ∑ j ∈ Finset.range n, f j omega)
        ((2 * q : ℕ) : ENNReal) μ ≤
        ∑' j : ℕ, ENNReal.ofReal (prefix_even_series_bound M s q j) := by
    intro n
    have hfinite := eLpNorm_sum_le (μ := μ) (f := f) (s := Finset.range n) hp
    have hfun : (∑ j ∈ Finset.range n, f j) =
        (fun omega => ∑ j ∈ Finset.range n, f j omega) := by
      funext omega
      simp only [Finset.sum_apply]
    rw [hfun] at hfinite
    calc
      eLpNorm (fun omega => ∑ j ∈ Finset.range n, f j omega)
        ((2 * q : ℕ) : ENNReal) μ ≤
        ∑ j ∈ Finset.range n,
          eLpNorm (f j) ((2 * q : ℕ) : ENNReal) μ := hfinite
      _ ≤ ∑ j ∈ Finset.range n,
        ENNReal.ofReal (prefix_even_series_bound M s q j) := by
          apply Finset.sum_le_sum
          intro j _
          exact prefix_eta_real_Fmaj_eLpNorm_even M s eta hEta N m j z q hq
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (prefix_even_series_bound M s q j) :=
        ENNReal.sum_le_tsum (Finset.range n)
  exact prefix_eLpNorm_tsum_le μ f ((2 * q : ℕ) : ENNReal) _ hf hpoint hbound


/-- Cutoff-uniform fixed-even-order bound for the exact raw field score. -/
theorem prefix_eta_raw_Fsc_eLpNorm_even {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (N m : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun omega : BilateralField d => (F N m z omega).toReal)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
        ∑' j : ℕ, ENNReal.ofReal (prefix_even_series_bound M s q j) := by
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hpush : ∀ᵐ potential ∂Measure.map (eta N) μ,
      (∑' j : ℕ, prefix_bank_Fmaj s m z j potential) ≠ ⊤ := by
    dsimp [μ]
    rw [prefix_eta_law M eta hEta N]
    exact prefix_bank_Fmaj_tsum_ae M s hs m z
  have htail := ae_of_ae_map (prefix_eta_aemeasurable M eta hEta N) hpush
  have hpoint : ∀ᵐ omega ∂μ,
      ‖(F N m z omega).toReal‖ ≤
        ‖∑' j : ℕ, prefix_real_Fmaj s m z j (eta N omega)‖ := by
    filter_upwards [hPrimitive, htail] with omega hp ht
    have hFle := prefix_raw_Fsc_le_tsum M s eps (eta N omega)
      (fun m y => F N m y omega) (fun m y => Praw N m y omega)
      (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
      (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)
      (hp N) m z
    have hreal : (∑' j : ℕ,
        prefix_bank_Fmaj s m z j (eta N omega)).toReal =
        ∑' j : ℕ, prefix_real_Fmaj s m z j (eta N omega) := by
      rw [ENNReal.tsum_toReal_eq
        (fun j => ENNReal.ne_top_of_tsum_ne_top ht j)]
      simp_rw [prefix_bank_Fmaj_toReal_eq]
    have hcomp := ENNReal.toReal_mono ht hFle
    rw [hreal] at hcomp
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (by rw [← hreal]; exact ENNReal.toReal_nonneg)]
    exact hcomp
  exact (SubdiffusiveProcess.RawLp.eLpNorm_mono_ae hpoint).trans
    ((SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _).trans
      (prefix_eta_real_Fmaj_tsum_eLpNorm_even
        M s hs eta hEta N m z q hq))


end Paper
