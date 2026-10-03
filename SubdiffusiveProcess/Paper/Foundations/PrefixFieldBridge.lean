module

public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldEvenFinite
public import SubdiffusiveProcess.PrefixMonotoneLp
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualFMeas

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess

namespace Paper

/-- The exact frozen raw field-score coordinate (`Sum.inl 0`), read along any
strictly increasing cutoff sequence `phi`, is Cauchy in `L^p` for every real
`p ≥ 1`.  Only the principal `hEta`/`hPrimitive` inputs and `s > 0` are used. -/
theorem aux_prefix_exact_Fsc_value_Lp_cauchy {d : ℕ} [NeZero d]
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
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (p : ℝ) (hp : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (F (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z) omega).toReal
          else 0) -
        (if n ≤ (phi k' : ℤ) then
          (F (phi k') ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z) omega).toReal
          else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let v : ℕ → BilateralField d → ℝ := fun N omega =>
    if n ≤ (N : ℤ) then
      (F N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal else 0
  -- A fixed even exponent `2q ≥ p`, chosen before disorder.
  let q : ℕ := ⌈p⌉₊
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr
    (Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hp)).ne'
  have hpq : ENNReal.ofReal p ≤ ((2 * q : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    have h1 : p ≤ (q : ℝ) := Nat.le_ceil p
    have h2 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    push_cast
    linarith
  let C : ℝ≥0∞ := ∑' j : ℕ, ENNReal.ofReal (prefix_even_series_bound M s q j)
  have hC : C ≠ ⊤ := prefix_even_series_tsum_ne_top M s hs q
  have hv (N : ℕ) : AEStronglyMeasurable (v N) μ := by
    by_cases hn : n ≤ (N : ℤ)
    · simpa only [v, if_pos hn] using
        (aux_lem_prefix_limit_actual_Fsc_raw_aemeas M s eps μ eta
          (fun N => prefix_eta_aemeasurable M eta hEta N)
          F Praw Rraw Draw Z rawGood hPrimitive N
          ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)).aestronglyMeasurable
    · simp only [v, if_neg hn]
      exact aestronglyMeasurable_const
  have hbound (N : ℕ) : eLpNorm (v N) (ENNReal.ofReal p) μ ≤ C := by
    refine (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans ?_
    by_cases hn : n ≤ (N : ℤ)
    · have hraw := prefix_eta_raw_Fsc_eLpNorm_even M s eps hs eta hEta
          F Praw Rraw Draw Z rawGood hPrimitive N
          ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) q hq
      rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (by simpa only [v, μ, if_pos hn] using! hv N)] at hraw
      simpa only [v, μ, C, if_pos hn] using! hraw
    · simp [v, if_neg hn]
  have hnn : ∀ᵐ omega ∂μ, ∀ k, 0 ≤ v (phi k) omega := by
    refine Eventually.of_forall fun omega k => ?_
    by_cases hn : n ≤ ((phi k : ℕ) : ℤ)
    · simp only [v, if_pos hn]
      exact ENNReal.toReal_nonneg
    · simp only [v, if_neg hn, le_refl]
  have hmono : ∀ᵐ omega ∂μ, Monotone (fun k => v (phi k) omega) := by
    have h := prefix_eta_raw_Fsc_value_mono_ae M s eps hs eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive n z
    filter_upwards [h] with omega hω
    exact hω.comp hphi.monotone
  simpa only [μ, v] using
    aux_prefix_field_mono_Lp_cauchy μ (fun k => v (phi k)) p hp
      (fun k => hv (phi k)) hnn hmono C hC (fun k => hbound (phi k)) eps0 heps0


end Paper
