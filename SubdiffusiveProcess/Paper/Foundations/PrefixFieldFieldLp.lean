import SubdiffusiveProcess.Paper.Foundations.PrefixFieldNumeric
import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport

noncomputable section

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper

theorem prefix_eta_bank_raw_window_eLpNorm_two {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j i : ℕ) (hi : i ∈ Finset.Icc (m - j) (m + j))
    (z : Vec d) :
    eLpNorm (fun omega : BilateralField d =>
      aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega))
      2 (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) *
        ENNReal.ofReal (2 * (1 + prefix_log_card d j)) := by
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
  have hL := prefix_log_card_nonneg d j
  calc
    eLpNorm (fun omega : BilateralField d =>
      aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega))
      2 (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) *
        eLpNorm (fun omega : BilateralField d =>
          aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
            aux_psf_sigma M) 2 (chaosSampleLaw M).toMeasure :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (Filter.Eventually.of_forall hpoint) 2
    _ ≤ ENNReal.ofReal (aux_psf_sigma M) *
      (2 * ENNReal.ofReal (2 + prefix_log_card d j)) ^ (1 / (2 : ℝ)) := by
        gcongr
        simpa only [prefix_log_card, Nat.cast_one, one_add_one_eq_two,
          pow_one, mul_one] using
          (prefix_eta_bank_raw_window_eLpNorm M eta hEta N m j i hi z 1 (by omega))
    _ ≤ ENNReal.ofReal (aux_psf_sigma M) *
      ENNReal.ofReal (2 * (1 + prefix_log_card d j)) := by
        gcongr
        exact prefix_sqrt_linear (prefix_log_card d j) hL


theorem prefix_eta_bank_raw_window_eLpNorm_two_sum {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j : ℕ) (z : Vec d) :
    eLpNorm (fun omega : BilateralField d =>
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega))
      2 (chaosSampleLaw M).toMeasure ≤
      ((Finset.Icc (m - j) (m + j)).card : ENNReal) *
        (ENNReal.ofReal (aux_psf_sigma M) *
          ENNReal.ofReal (2 * (1 + prefix_log_card d j))) := by
  let f : ℕ → BilateralField d → ℝ := fun i omega =>
    aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega)
  have hmeas : ∀ i ∈ Finset.Icc (m - j) (m + j),
      AEStronglyMeasurable (f i) (chaosSampleLaw M).toMeasure := by
    intro i _
    exact ((prefix_bank_maxObs_measurable i (m + 1 + j) z).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
  have hsum := eLpNorm_sum_le (f := f) hmeas (by norm_num : (1 : ENNReal) ≤ 2)
  have hfun : (∑ i ∈ Finset.Icc (m - j) (m + j), f i) =
      (fun omega => ∑ i ∈ Finset.Icc (m - j) (m + j), f i omega) := by
    funext omega
    simp only [Finset.sum_apply]
  rw [hfun] at hsum
  calc
    eLpNorm (fun omega : BilateralField d =>
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega))
      2 (chaosSampleLaw M).toMeasure ≤
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        eLpNorm (f i) 2 (chaosSampleLaw M).toMeasure := hsum
    _ ≤ ∑ _i ∈ Finset.Icc (m - j) (m + j),
      ENNReal.ofReal (aux_psf_sigma M) *
        ENNReal.ofReal (2 * (1 + prefix_log_card d j)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact prefix_eta_bank_raw_window_eLpNorm_two M eta hEta N m j i hi z
    _ = ((Finset.Icc (m - j) (m + j)).card : ENNReal) *
        (ENNReal.ofReal (aux_psf_sigma M) *
          ENNReal.ofReal (2 * (1 + prefix_log_card d j))) := by
            rw [Finset.sum_const, nsmul_eq_mul]


noncomputable def prefix_real_Fmaj {d : ℕ} (s : ℝ) (m : ℕ)
    (z : Vec d) (j : ℕ) (omega : PotentialSample d) : ℝ :=
  (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) *
    ∑ i ∈ Finset.Icc (m - j) (m + j),
      aux_prefix_bank_maxObs i (m + 1 + j) z omega

theorem prefix_eta_real_Fmaj_eLpNorm_two {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j : ℕ) (z : Vec d) :
    eLpNorm (fun omega : BilateralField d =>
      prefix_real_Fmaj s m z j (eta N omega)) 2
      (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (prefix_L2_series_bound M s j) := by
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
      prefix_real_Fmaj s m z j (eta N omega)) 2
      (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal c * eLpNorm g 2 (chaosSampleLaw M).toMeasure :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (Filter.Eventually.of_forall hpoint) 2
    _ ≤ ENNReal.ofReal c *
        (((Finset.Icc (m - j) (m + j)).card : ENNReal) *
          (ENNReal.ofReal (aux_psf_sigma M) *
            ENNReal.ofReal (2 * (1 + prefix_log_card d j)))) := by
          gcongr
          exact prefix_eta_bank_raw_window_eLpNorm_two_sum M eta hEta N m j z
    _ ≤ ENNReal.ofReal c *
        (ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ)) *
          (ENNReal.ofReal (aux_psf_sigma M) *
            ENNReal.ofReal (2 * (1 + prefix_log_card d j)))) := by gcongr
    _ = ENNReal.ofReal (prefix_L2_series_bound M s j) := by
      dsimp [prefix_L2_series_bound, c]
      rw [← ENNReal.ofReal_mul (aux_psf_sigma_pos M).le,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      congr 1
      ring


theorem prefix_bank_Fmaj_toReal_eq {d : ℕ} (s : ℝ) (m : ℕ)
    (z : Vec d) (j : ℕ) (omega : PotentialSample d) :
    (prefix_bank_Fmaj s m z j omega).toReal =
      prefix_real_Fmaj s m z j omega := by
  unfold prefix_bank_Fmaj prefix_real_Fmaj
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)]
  rw [ENNReal.toReal_sum]
  · simp_rw [ENNReal.toReal_ofReal
      (prefix_bank_maxObs_nonneg _ _ _ _)]
  · intro i _
    exact ENNReal.ofReal_ne_top


theorem prefix_real_Fmaj_measurable {d : ℕ} (s : ℝ) (m : ℕ)
    (z : Vec d) (j : ℕ) :
    Measurable (fun omega : PotentialSample d =>
      prefix_real_Fmaj s m z j omega) := by
  unfold prefix_real_Fmaj
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact prefix_bank_maxObs_measurable i (m + 1 + j) z


theorem prefix_eta_real_Fmaj_tsum_eLpNorm_two {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m : ℕ) (z : Vec d) :
    eLpNorm (fun omega : BilateralField d =>
      ∑' j : ℕ, prefix_real_Fmaj s m z j (eta N omega))
      2 (chaosSampleLaw M).toMeasure ≤
        ∑' j : ℕ, ENNReal.ofReal (prefix_L2_series_bound M s j) := by
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
  have hbound : ∀ n : ℕ,
      eLpNorm (fun omega => ∑ j ∈ Finset.range n, f j omega) 2 μ ≤
        ∑' j : ℕ, ENNReal.ofReal (prefix_L2_series_bound M s j) := by
    intro n
    have hfinite := eLpNorm_sum_le (f := f) (s := Finset.range n)
      (fun j _ => hf j) (by norm_num : (1 : ENNReal) ≤ 2)
    have hfun : (∑ j ∈ Finset.range n, f j) =
        (fun omega => ∑ j ∈ Finset.range n, f j omega) := by
      funext omega
      simp only [Finset.sum_apply]
    rw [hfun] at hfinite
    calc
      eLpNorm (fun omega => ∑ j ∈ Finset.range n, f j omega) 2 μ ≤
        ∑ j ∈ Finset.range n, eLpNorm (f j) 2 μ := hfinite
      _ ≤ ∑ j ∈ Finset.range n,
        ENNReal.ofReal (prefix_L2_series_bound M s j) := by
          apply Finset.sum_le_sum
          intro j _
          exact prefix_eta_real_Fmaj_eLpNorm_two M s eta hEta N m j z
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (prefix_L2_series_bound M s j) :=
        ENNReal.sum_le_tsum (Finset.range n)
  exact prefix_eLpNorm_tsum_le μ f 2 _ hf hpoint hbound


/-- Cutoff-uniform `L²` bound for the actual finite real raw field score.
The right side depends on `M`, `s`, and `d`, but not `N`, `m`, or `z`. -/
theorem prefix_eta_raw_Fsc_eLpNorm_two {d : ℕ} [NeZero d]
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
    (N m : ℕ) (z : Vec d) :
    eLpNorm (fun omega : BilateralField d => (F N m z omega).toReal)
      2 (chaosSampleLaw M).toMeasure ≤
        ∑' j : ℕ, ENNReal.ofReal (prefix_L2_series_bound M s j) := by
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
  exact (eLpNorm_mono_ae hpoint).trans
    (prefix_eta_real_Fmaj_tsum_eLpNorm_two M s hs eta hEta N m z)


theorem prefix_L2_series_tsum_ne_top {d : ℕ} (M : GMCModel d)
    (s : ℝ) (hs : 0 < s) :
    (∑' j : ℕ, ENNReal.ofReal (prefix_L2_series_bound M s j)) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (prefix_L2_series_bound_nonneg M s)
    (prefix_L2_series_bound_summable M s hs)]
  exact ENNReal.ofReal_ne_top


/-- The exact rescaled raw `jj=0` coordinate is nondecreasing along every
cutoff, almost surely. The inactive values before the level is reached are
zero, exactly as in the frozen `value` definition. -/
theorem prefix_eta_raw_Fsc_value_mono_ae {d : ℕ} [NeZero d]
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
    (n : ℤ) (z : Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Monotone (fun N : ℕ => if n ≤ (N : ℤ) then
        (F N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal
        else 0) := by
  have hfinite : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N : ℕ,
        F N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega ≠ ⊤ := by
    rw [ae_all_iff]
    intro N
    exact prefix_eta_raw_Fsc_ae_finite M s eps hs eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive N
      ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
  filter_upwards [hEta, hPrimitive, hfinite] with omega he hp hf
  intro N N' hNN'
  by_cases hn : n ≤ (N : ℤ)
  · have hn' : n ≤ (N' : ℤ) := by
      have hcast : (N : ℤ) ≤ (N' : ℤ) := by omega
      exact hn.trans hcast
    simp only [if_pos hn, if_pos hn']
    have hmono := (aux_lem_prefix_limit_actual_coordinate_cauchy_raw_mono
      M s eps omega eta he F Praw Rraw Draw Z rawGood hp
      n z N N' hn hNN').1
    exact ENNReal.toReal_mono (hf N') hmono
  · by_cases hn' : n ≤ (N' : ℤ)
    · simp only [if_neg hn, if_pos hn']
      exact ENNReal.toReal_nonneg
    · simp only [if_neg hn, if_neg hn']
      exact le_refl 0


end Paper
