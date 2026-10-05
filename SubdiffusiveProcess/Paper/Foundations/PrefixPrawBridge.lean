module

public import SubdiffusiveProcess.Paper.Foundations.PrefixPrawUniform
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport
public import SubdiffusiveProcess.PrefixMonotoneLp
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualPrawMeas

@[expose] public section

/-!
# The exact raw product coordinate (`Sum.inl 1`, `Praw`) is `L^p`-Cauchy

The actual coupled `Praw N m w` is, almost surely, the literal `Psc` functional of
`eta N omega`, whose law is `M.P` for every cutoff `N` (`prefix_eta_law`).  Hence the
cutoff-uniform moment bound of `PrawUniform` transfers verbatim, uniformly in `N`, `m`
and `w`.  The disorder threshold `aux_prefix_praw_delta0 d s moments` depends only on the
dimension, `s`, and the finite moment list.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper

/-! ### The threshold, chosen after the finite moment list -/

/-- The moment exponent `R`: at least every requested moment, and `32 (d+1) / s`. -/
def aux_prefix_praw_R (d : ℕ) (s : ℝ) (moments : Finset ℝ) : ℝ :=
  32 * ((d : ℝ) + 1) / s + ∑ p ∈ moments, |p| + 1

/-- The disorder threshold for the raw product coordinate. -/
def aux_prefix_praw_delta0 (d : ℕ) (s : ℝ) (moments : Finset ℝ) : ℝ :=
  Real.sqrt (s / (16 * aux_prefix_praw_R d s moments)) / (1 + (d : ℝ))

theorem aux_prefix_praw_R_one_le (d : ℕ) (s : ℝ) (hs : 0 < s) (moments : Finset ℝ) :
    1 ≤ aux_prefix_praw_R d s moments := by
  unfold aux_prefix_praw_R
  have h1 : 0 ≤ 32 * ((d : ℝ) + 1) / s := by positivity
  have h2 : 0 ≤ ∑ p ∈ moments, |p| := Finset.sum_nonneg (fun p _ => abs_nonneg p)
  linarith

theorem aux_prefix_praw_R_budget (d : ℕ) (s : ℝ) (hs : 0 < s) (moments : Finset ℝ) :
    32 * ((d : ℝ) + 1) ≤ s * aux_prefix_praw_R d s moments := by
  unfold aux_prefix_praw_R
  have h2 : 0 ≤ ∑ p ∈ moments, |p| := Finset.sum_nonneg (fun p _ => abs_nonneg p)
  have h3 : s * (32 * ((d : ℝ) + 1) / s) = 32 * ((d : ℝ) + 1) := by field_simp
  nlinarith

theorem aux_prefix_praw_le_R (d : ℕ) (s : ℝ) (hs : 0 < s) (moments : Finset ℝ) (p : ℝ)
    (hp : p ∈ insert 1 moments) : p ≤ aux_prefix_praw_R d s moments := by
  have h1 : 0 ≤ 32 * ((d : ℝ) + 1) / s := by positivity
  have h2 : 0 ≤ ∑ p ∈ moments, |p| := Finset.sum_nonneg (fun p _ => abs_nonneg p)
  unfold aux_prefix_praw_R
  rcases Finset.mem_insert.mp hp with h | h
  · rw [h]; linarith
  · have h3 : |p| ≤ ∑ p ∈ moments, |p| :=
      Finset.single_le_sum (f := fun p => |p|) (fun p _ => abs_nonneg p) h
    have h4 := le_abs_self p
    linarith

theorem aux_prefix_praw_delta0_pos (d : ℕ) (s : ℝ) (hs : 0 < s) (moments : Finset ℝ) :
    0 < aux_prefix_praw_delta0 d s moments := by
  have hR := aux_prefix_praw_R_one_le d s hs moments
  unfold aux_prefix_praw_delta0
  have : 0 < s / (16 * aux_prefix_praw_R d s moments) := by positivity
  positivity

/-- Below the threshold the disorder budget `16 R σ² ≤ s` holds. -/
theorem aux_prefix_praw_sigma_budget {d : ℕ} (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (moments : Finset ℝ) (hM : M.delta ≤ aux_prefix_praw_delta0 d s moments) :
    16 * aux_prefix_praw_R d s moments * aux_psf_sigma M ^ 2 ≤ s := by
  have hR := aux_prefix_praw_R_one_le d s hs moments
  set R := aux_prefix_praw_R d s moments with hRdef
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hd1 : (0 : ℝ) < 1 + (d : ℝ) := by positivity
  have hσ0 : 0 ≤ aux_psf_sigma M := (aux_psf_sigma_pos M).le
  have hσle : aux_psf_sigma M ≤ Real.sqrt (s / (16 * R)) := by
    unfold aux_psf_sigma
    unfold aux_prefix_praw_delta0 at hM
    rw [← hRdef] at hM
    rw [le_div_iff₀ hd1] at hM
    linarith
  have hsq : aux_psf_sigma M ^ 2 ≤ s / (16 * R) := by
    have h := pow_le_pow_left₀ hσ0 hσle 2
    rwa [Real.sq_sqrt (by positivity)] at h
  have h16 : 0 < 16 * R := by positivity
  rw [le_div_iff₀ h16] at hsq
  linarith

theorem aux_prefix_praw_one_le_dim {d : ℕ} [NeZero d] : (1 : ℝ) ≤ (d : ℝ) := by
  have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  exact_mod_cast this

/-! ### Transport to the actual coupled coordinate -/

variable {d : ℕ} [NeZero d]
  [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Almost surely the actual `Praw` is the literal product score of `eta N omega`. -/
theorem aux_prefix_praw_actual_ae_eq (M : GMCModel d) (s eps : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (N m : ℕ) (w : Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Praw N m w omega = aux_prefix_praw_PscF s m w (eta N omega) := by
  filter_upwards [hPrimitive] with omega hps
  have hprim := hps N
  rw [_root_.SubdiffusiveProcess.Paper.primitive_scores] at hprim
  obtain ⟨_, _, _, _, _, hP, _, _, _, _, _⟩ := hprim
  exact hP m w

/-- **Cutoff-uniform `R`-th moment of the actual `Praw`**: the same explicit series bounds
every cutoff `N`, depth `m` and centre `w`. -/
theorem aux_prefix_praw_actual_rpow_lintegral_le (M : GMCModel d) (s eps R : ℝ)
    (hR : 1 ≤ R)
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
    (N m : ℕ) (w : Vec d) :
    (∫⁻ omega, (Praw N m w omega) ^ R ∂(chaosSampleLaw M).toMeasure) ≤
      ∑' j : ℕ, ENNReal.ofReal
        (aux_prefix_praw_term d s R (aux_psf_sigma M) (aux_prefix_praw_CB M R) j) := by
  have hmeas : Measurable (fun g : PotentialSample d => (aux_prefix_praw_PscF s m w g) ^ R) :=
    (aux_lem_prefix_limit_actual_Psc_meas s m w).pow_const R
  have hae := aux_prefix_praw_actual_ae_eq M s eps eta F Praw Rraw Draw Z rawGood
    hPrimitive N m w
  calc (∫⁻ omega, (Praw N m w omega) ^ R ∂(chaosSampleLaw M).toMeasure) =
        ∫⁻ omega, (aux_prefix_praw_PscF s m w (eta N omega)) ^ R
          ∂(chaosSampleLaw M).toMeasure :=
        lintegral_congr_ae (hae.mono fun omega h => by dsimp only; rw [h])
    _ = ∫⁻ g, (aux_prefix_praw_PscF s m w g) ^ R
          ∂Measure.map (eta N) (chaosSampleLaw M).toMeasure :=
        (lintegral_map' hmeas.aemeasurable (prefix_eta_aemeasurable M eta hEta N)).symm
    _ = ∫⁻ g, (aux_prefix_praw_PscF s m w g) ^ R ∂M.P.toMeasure := by
        rw [prefix_eta_law M eta hEta N]
    _ ≤ _ := aux_prefix_praw_PscF_rpow_lintegral_le aux_prefix_praw_one_le_dim M s R hR m w

/-- The uniform `L^p` bound of the real-valued actual coordinate, for every `0 < p ≤ R`. -/
theorem aux_prefix_praw_actual_eLpNorm_le (M : GMCModel d) (s eps R : ℝ)
    (hR : 1 ≤ R)
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
    (N m : ℕ) (w : Vec d) (p : ℝ) (hpR : p ≤ R) :
    eLpNorm (fun omega => (Praw N m w omega).toReal) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤
      (∑' j : ℕ, ENNReal.ofReal
        (aux_prefix_praw_term d s R (aux_psf_sigma M) (aux_prefix_praw_CB M R) j)) ^ (1 / R) := by
  have hR0 : 0 < R := by linarith
  have hmeas : AEStronglyMeasurable (fun omega => (Praw N m w omega).toReal)
      (chaosSampleLaw M).toMeasure :=
    (aux_lem_prefix_limit_actual_Praw_raw_aemeas M s eps (chaosSampleLaw M).toMeasure eta
      (fun N => prefix_eta_aemeasurable M eta hEta N)
      F Praw Rraw Draw Z rawGood hPrimitive N m w).aestronglyMeasurable
  refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpR)).trans ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hR0) ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal hR0.le]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  refine le_trans (lintegral_mono fun omega => ?_)
    (aux_prefix_praw_actual_rpow_lintegral_le M s eps R hR eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive N m w)
  refine ENNReal.rpow_le_rpow ?_ hR0.le
  rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

/-- Under the threshold the actual `Praw` is almost surely finite at every cutoff. -/
theorem aux_prefix_praw_actual_ae_finite (M : GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (moments : Finset ℝ) (hM : M.delta ≤ aux_prefix_praw_delta0 d s moments)
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
    (N m : ℕ) (w : Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, Praw N m w omega ≠ ⊤ := by
  set R := aux_prefix_praw_R d s moments with hRdef
  have hR := aux_prefix_praw_R_one_le d s hs moments
  have hR0 : 0 < R := by linarith
  have hfin := aux_prefix_praw_series_ne_top M s R hs hR
    (aux_prefix_praw_R_budget d s hs moments) (aux_prefix_praw_sigma_budget M s hs moments hM)
  have hint : (∫⁻ omega, (Praw N m w omega) ^ R ∂(chaosSampleLaw M).toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (aux_prefix_praw_actual_rpow_lintegral_le M s eps R hR eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive N m w)
  have hae := aux_prefix_praw_actual_ae_eq M s eps eta F Praw Rraw Draw Z rawGood
    hPrimitive N m w
  have hPmeas : AEMeasurable (fun omega => Praw N m w omega) (chaosSampleLaw M).toMeasure :=
    ((aux_lem_prefix_limit_actual_Psc_meas s m w).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).congr (hae.mono fun omega h => h.symm)
  filter_upwards [ae_lt_top' (hPmeas.pow_const R) hint] with omega hlt
  intro htop
  rw [htop, ENNReal.top_rpow_of_pos hR0] at hlt
  exact lt_irrefl _ hlt

/-- The exact frozen raw product coordinate is almost surely nondecreasing in the cutoff. -/
theorem aux_prefix_praw_value_mono_ae (M : GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (moments : Finset ℝ) (hM : M.delta ≤ aux_prefix_praw_delta0 d s moments)
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
        (Praw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal
        else 0) := by
  have hfinite : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N : ℕ, Praw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega ≠ ⊤ := by
    rw [ae_all_iff]
    intro N
    exact aux_prefix_praw_actual_ae_finite M s eps hs moments hM eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
  filter_upwards [hEta, hPrimitive, hfinite] with omega he hp hf
  intro N N' hNN'
  by_cases hn : n ≤ (N : ℤ)
  · have hn' : n ≤ (N' : ℤ) := by
      have hcast : (N : ℤ) ≤ (N' : ℤ) := by omega
      exact hn.trans hcast
    simp only [ite_eq_left hn, ite_eq_left hn']
    have hmono := (aux_lem_prefix_limit_actual_coordinate_cauchy_raw_mono
      M s eps omega eta he F Praw Rraw Draw Z rawGood hp n z N N' hn hNN').2
    exact ENNReal.toReal_mono (hf N') hmono
  · by_cases hn' : n ≤ (N' : ℤ)
    · simp only [ite_eq_right hn, ite_eq_left hn']
      exact ENNReal.toReal_nonneg
    · simp only [ite_eq_right hn, ite_eq_right hn']
      exact le_refl 0

/-- **The exact frozen raw product coordinate (`Sum.inl 1`) is `L^p`-Cauchy** along any
strictly increasing cutoff sequence, for every requested moment `p`, once the disorder is
below the threshold `aux_prefix_praw_delta0 d s moments` (chosen after the moment list,
before the model). -/
theorem aux_prefix_exact_Praw_value_Lp_cauchy (M : GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (moments : Finset ℝ) (hM : M.delta ≤ aux_prefix_praw_delta0 d s moments)
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
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (p : ℝ) (hp : p ∈ insert 1 moments) (hp1 : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (Praw (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z) omega).toReal
          else 0) -
        (if n ≤ (phi k' : ℤ) then
          (Praw (phi k') ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z) omega).toReal
          else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let v : ℕ → BilateralField d → ℝ := fun N omega =>
    if n ≤ (N : ℤ) then
      (Praw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal else 0
  set R := aux_prefix_praw_R d s moments with hRdef
  have hR := aux_prefix_praw_R_one_le d s hs moments
  have hpR : p ≤ R := aux_prefix_praw_le_R d s hs moments p hp
  let C : ℝ≥0∞ := (∑' j : ℕ, ENNReal.ofReal
    (aux_prefix_praw_term d s R (aux_psf_sigma M) (aux_prefix_praw_CB M R) j)) ^ (1 / R)
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (aux_prefix_praw_series_ne_top M s R hs hR (aux_prefix_praw_R_budget d s hs moments)
      (aux_prefix_praw_sigma_budget M s hs moments hM))
  have hv (N : ℕ) : AEStronglyMeasurable (v N) μ := by
    by_cases hn : n ≤ (N : ℤ)
    · simpa only [v, ite_eq_left hn] using
        (aux_lem_prefix_limit_actual_Praw_raw_aemeas M s eps μ eta
          (fun N => prefix_eta_aemeasurable M eta hEta N)
          F Praw Rraw Draw Z rawGood hPrimitive N
          ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)).aestronglyMeasurable
    · simp only [v, ite_eq_right hn]
      exact aestronglyMeasurable_const
  have hbound (N : ℕ) : eLpNorm (v N) (ENNReal.ofReal p) μ ≤ C := by
    by_cases hn : n ≤ (N : ℤ)
    · simpa only [v, μ, C, ite_eq_left hn] using
        aux_prefix_praw_actual_eLpNorm_le M s eps R hR eta hEta
          F Praw Rraw Draw Z rawGood hPrimitive N
          ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) p hpR
    · simp [v, ite_eq_right hn]
  have hnn : ∀ᵐ omega ∂μ, ∀ k, 0 ≤ v (phi k) omega := by
    refine Eventually.of_forall fun omega k => ?_
    by_cases hn : n ≤ ((phi k : ℕ) : ℤ)
    · simp only [v, ite_eq_left hn]
      exact ENNReal.toReal_nonneg
    · simp only [v, ite_eq_right hn, le_refl]
  have hmono : ∀ᵐ omega ∂μ, Monotone (fun k => v (phi k) omega) := by
    have h := aux_prefix_praw_value_mono_ae M s eps hs moments hM eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive n z
    filter_upwards [h] with omega hω
    exact hω.comp hphi.monotone
  simpa only [μ, v] using
    aux_prefix_field_mono_Lp_cauchy μ (fun k => v (phi k)) p hp1
      (fun k => hv (phi k)) hnn hmono C hC (fun k => hbound (phi k)) eps0 heps0

end SubdiffusiveProcess.Paper
