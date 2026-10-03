module

public import SubdiffusiveProcess.Paper.lfgc_fp_det
public import SubdiffusiveProcess.Paper.lfgc_fp_events
public import SubdiffusiveProcess.Lfgc.FPNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Pad-test pieces: probability of one window

For the pad level `n`, a centre `y` and a window index `h = j + 1`, the three pieces of the
pad-test cover are: the field-test layer banks of depth `j`, the product-window bank of depth
`j`, and the tail-layer banks `(j', l)` with `j' + l + 1 = h`.  Under explicit smallness of the
bank scale `σ_M` (and `Λ σ_M ≤ 1` for the moment order `Λ` of `amaj_num`), each piece has
probability at most `e^{-R h}/(6 (ns+1))`.
-/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_fp_bound_cells_card_le_nine (a j : ℕ) (ha : a ≤ 2 * j + 1) :
    ((Paper.aux_psf_cells d a).card : ℝ) ≤ (9 : ℝ) ^ (d * (j + 1)) := by
  rw [Paper.aux_psf_cells_card, pow_mul']
  push_cast
  refine pow_le_pow_left₀ (by positivity) ?_ d
  have h1 : (3 : ℝ) ^ a ≤ (3 : ℝ) ^ (2 * j + 1) := pow_le_pow_right₀ (by norm_num) ha
  have h2 : (9 : ℝ) ^ (j + 1) = 3 * (3 : ℝ) ^ (2 * j + 1) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ]
    ring
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * j + 1) := one_le_pow₀ (by norm_num)
  rw [h2]
  linarith

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_fp_bound_cells_card_le_seven (a : ℕ) (ha : a ≤ 1) :
    ((Paper.aux_psf_cells d a).card : ℝ) ≤ (7 : ℝ) ^ d := by
  rw [Paper.aux_psf_cells_card]
  push_cast
  refine pow_le_pow_left₀ (by positivity) ?_ d
  have : (3 : ℝ) ^ a ≤ 3 := by
    calc (3 : ℝ) ^ a ≤ 3 ^ 1 := pow_le_pow_right₀ (by norm_num) ha
      _ = 3 := pow_one 3
  linarith

theorem aux_lfgc_fp_bound_two_mul_add_one_le_three_pow (j : ℕ) : (2 * (j : ℝ) + 1) ≤ (3 : ℝ) ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ n ih =>
      push_cast at ih ⊢
      rw [pow_succ]
      have : (1 : ℝ) ≤ (3 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
      linarith

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Union bound over a finset with a uniform bound. -/
theorem aux_lfgc_fp_bound_measure_biUnion_le_card {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : Finset ι)
    (E : ι → Set Ω) {x : ℝ≥0∞} (hx : ∀ i ∈ S, μ (E i) ≤ x) :
    μ (⋃ i ∈ S, E i) ≤ S.card * x :=
  (measure_biUnion_finset_le S E).trans (by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul S _ x hx)

/-- The field-test piece of depth `j`. -/
theorem lfgc_fp_bound (M : GMCModel d) (s : ℝ) (hs : 0 < s) (ns : ℕ) {R : ℝ}
    (hsmall : Real.log (6 * (2 * ((ns : ℝ) + 1))) + Real.log (3 * 9 ^ d) + R ≤
      (Real.exp (-(s * Real.log 3 / 8)) * (s * Real.log 3 / 8) ^ 2 / 4 /
        Paper.aux_psf_sigma M) ^ 2)
    (N n j : ℕ) (y : Vec d) :
    ((ns : ℝ≥0∞) + 1) * (chaosSampleLaw M).toMeasure
      (⋃ i ∈ Finset.Icc (n - j) (n + j),
        aux_lfgc_fp_events_bankEv N i (n + 1 + j) y ((3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1))) ≤
      ENNReal.ofReal (Real.exp (-R * ((j + 1 : ℕ) : ℝ)) / 6) := by
  have hσ := Paper.aux_psf_sigma_pos M
  set t := (3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1) with htdef
  have ht0 : 0 ≤ t := by positivity
  set g := Real.exp (-(t / Paper.aux_psf_sigma M) ^ 2) with hg
  have hterm : ∀ i ∈ Finset.Icc (n - j) (n + j),
      (chaosSampleLaw M).toMeasure (aux_lfgc_fp_events_bankEv N i (n + 1 + j) y t) ≤
        ENNReal.ofReal ((9 : ℝ) ^ (d * (j + 1)) * 2 * g) := by
    intro i hi
    refine (lfgc_fp_events M N i (n + 1 + j) y ht0).trans ?_
    have hc := aux_lfgc_fp_bound_cells_card_le_nine (d := d) (n + 1 + j - i) j (by
      have := (Finset.mem_Icc.mp hi).1; omega)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    gcongr
    · rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hc
    · norm_num
  have hU := aux_lfgc_fp_bound_measure_biUnion_le_card (chaosSampleLaw M).toMeasure _ _ hterm
  have hcard := aux_lfgc_fp_det_card_Icc_sub_add_le n j
  have hc0 : 0 < Real.exp (-(s * Real.log 3 / 8)) * (s * Real.log 3 / 8) ^ 2 / 4 := by
    have := Real.log_pos (show (1 : ℝ) < 3 by norm_num); positivity
  have hmain := gauss_tail_le hc0 hσ (K := 2 * ((ns : ℝ) + 1)) (Q := 3 * 9 ^ d) (R := R)
    (by linarith [(Nat.cast_nonneg ns : (0 : ℝ) ≤ ns)])
    (by have : (1 : ℝ) ≤ 9 ^ d := one_le_pow₀ (by norm_num); linarith) hsmall
    (h := j + 1) (by omega) (t := t) (by push_cast; exact fThreshold_ge hs j)
  calc ((ns : ℝ≥0∞) + 1) * (chaosSampleLaw M).toMeasure
        (⋃ i ∈ Finset.Icc (n - j) (n + j), aux_lfgc_fp_events_bankEv N i (n + 1 + j) y t)
      ≤ ((ns : ℝ≥0∞) + 1) * (((Finset.Icc (n - j) (n + j)).card : ℝ≥0∞) *
          ENNReal.ofReal ((9 : ℝ) ^ (d * (j + 1)) * 2 * g)) := by gcongr
    _ = ENNReal.ofReal (((ns : ℝ) + 1) * ((Finset.Icc (n - j) (n + j)).card *
          ((9 : ℝ) ^ (d * (j + 1)) * 2 * g))) := by
        have e1 : ((ns : ℝ≥0∞) + 1) = ENNReal.ofReal ((ns : ℝ) + 1) := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one]
        have e2 : (((Finset.Icc (n - j) (n + j)).card : ℕ) : ℝ≥0∞) =
            ENNReal.ofReal ((Finset.Icc (n - j) (n + j)).card : ℝ) :=
          (ENNReal.ofReal_natCast _).symm
        rw [e1, e2, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (Real.exp (-R * ((j + 1 : ℕ) : ℝ)) / 6) := by
        refine ENNReal.ofReal_le_ofReal (le_trans ?_ hmain)
        have h3 := aux_lfgc_fp_bound_two_mul_add_one_le_three_pow j
        have hg0 : 0 ≤ g := (Real.exp_pos _).le
        have hQ : (3 * (9 : ℝ) ^ d) ^ (j + 1) = (3 : ℝ) ^ (j + 1) * (9 : ℝ) ^ (d * (j + 1)) := by
          rw [mul_pow, ← pow_mul]
        rw [hQ]
        have h9 : 0 ≤ (9 : ℝ) ^ (d * (j + 1)) := by positivity
        have hns : (0 : ℝ) ≤ ns := Nat.cast_nonneg ns
        calc ((ns : ℝ) + 1) * ((Finset.Icc (n - j) (n + j)).card *
              ((9 : ℝ) ^ (d * (j + 1)) * 2 * g))
            ≤ ((ns : ℝ) + 1) * ((2 * j + 1) * ((9 : ℝ) ^ (d * (j + 1)) * 2 * g)) := by
              gcongr
          _ ≤ ((ns : ℝ) + 1) * ((3 : ℝ) ^ (j + 1) * ((9 : ℝ) ^ (d * (j + 1)) * 2 * g)) := by
              gcongr
          _ = 2 * ((ns : ℝ) + 1) * ((3 : ℝ) ^ (j + 1) * (9 : ℝ) ^ (d * (j + 1))) * g := by ring

/-- The product-window piece of depth `j`. -/
theorem aux_lfgc_fp_bound_aPiece_prob (M : GMCModel d) (s : ℝ) (hs : 0 < s) (ns : ℕ) {R Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hnum : ∀ j : ℕ, 6 * (ns + 1 : ℝ) * (9 : ℝ) ^ (d * (j + 1)) * (16 : ℝ) ^ (j + 1) ≤
        Real.exp (-R * ((j : ℝ) + 1)) * (6 ^ Λ * ((3 : ℝ) ^ (s * (j : ℝ) / 8)) ^ Λ))
    (hΛσ : Λ * Paper.aux_psf_sigma M ≤ 1) (N n j : ℕ) (y : Vec d) :
    ((ns : ℝ≥0∞) + 1) * (chaosSampleLaw M).toMeasure
      (aux_lfgc_fp_events_amajEv N n j y (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8))) ≤
      ENNReal.ofReal (Real.exp (-R * ((j + 1 : ℕ) : ℝ)) / 6) := by
  have hσ := Paper.aux_psf_sigma_pos M
  have hT : 0 < 6 * (3 : ℝ) ^ (s * (j : ℝ) / 8) := by positivity
  have hΛ0 : 0 < Λ := by linarith
  have hP := aux_lfgc_fp_events_amajEv_prob M N n j y hT hΛ0
  -- bound the numerator
  have hcard := aux_lfgc_fp_bound_cells_card_le_nine (d := d) (n + 1 + j - (n - j)) j (by omega)
  have hexp : Real.exp (Λ ^ 2 * Paper.aux_psf_sigma M ^ 2 / 4) * 2 ≤ 4 := by
    have h1 : Λ ^ 2 * Paper.aux_psf_sigma M ^ 2 / 4 ≤ 1 / 4 := by
      have := mul_le_mul hΛσ hΛσ (by positivity) zero_le_one
      nlinarith
    have h2 : Real.exp (1 / 4) ≤ 2 := by
      have := Real.log_two_gt_d9
      calc Real.exp (1 / 4) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
        _ = 2 := Real.exp_log (by norm_num)
    have := Real.exp_le_exp.mpr h1
    linarith
  have hIcc := aux_lfgc_fp_det_card_Icc_sub_add_le n j
  have hpow : (4 : ℝ) ^ ((Finset.Icc (n - j) (n + j)).card) ≤ (16 : ℝ) ^ (j + 1) := by
    have hc : (Finset.Icc (n - j) (n + j)).card ≤ 2 * (j + 1) := by
      have : ((Finset.Icc (n - j) (n + j)).card : ℝ) ≤ 2 * (j + 1) := by linarith
      exact_mod_cast this
    calc (4 : ℝ) ^ ((Finset.Icc (n - j) (n + j)).card) ≤ 4 ^ (2 * (j + 1)) :=
          pow_le_pow_right₀ (by norm_num) hc
      _ = 16 ^ (j + 1) := by rw [pow_mul]; norm_num
  have hnumE : ((Paper.aux_psf_cells d (n + 1 + j - (n - j))).card : ℝ≥0∞) *
      (ENNReal.ofReal (Real.exp (Λ ^ 2 * Paper.aux_psf_sigma M ^ 2 / 4)) * 2) ^
        ((Finset.Icc (n - j) (n + j)).card) ≤
      ENNReal.ofReal ((9 : ℝ) ^ (d * (j + 1)) * (16 : ℝ) ^ (j + 1)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    gcongr
    · rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hcard
    · calc (ENNReal.ofReal (Real.exp (Λ ^ 2 * Paper.aux_psf_sigma M ^ 2 / 4)) * 2) ^
            ((Finset.Icc (n - j) (n + j)).card)
          = ENNReal.ofReal ((Real.exp (Λ ^ 2 * Paper.aux_psf_sigma M ^ 2 / 4) * 2) ^
              ((Finset.Icc (n - j) (n + j)).card)) := by
            rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity)]
            norm_num
        _ ≤ ENNReal.ofReal ((4 : ℝ) ^ ((Finset.Icc (n - j) (n + j)).card)) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hexp _)
        _ ≤ ENNReal.ofReal ((16 : ℝ) ^ (j + 1)) := ENNReal.ofReal_le_ofReal hpow
  have hden : ENNReal.ofReal (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8)) ^ Λ =
      ENNReal.ofReal (6 ^ Λ * ((3 : ℝ) ^ (s * (j : ℝ) / 8)) ^ Λ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hT.le hΛ0.le, Real.mul_rpow (by norm_num) (by positivity)]
  have hdpos : 0 < 6 ^ Λ * ((3 : ℝ) ^ (s * (j : ℝ) / 8)) ^ Λ := by positivity
  have hnj := hnum j
  calc ((ns : ℝ≥0∞) + 1) * (chaosSampleLaw M).toMeasure
        (aux_lfgc_fp_events_amajEv N n j y (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8)))
      ≤ ((ns : ℝ≥0∞) + 1) * (ENNReal.ofReal ((9 : ℝ) ^ (d * (j + 1)) * (16 : ℝ) ^ (j + 1)) /
          ENNReal.ofReal (6 ^ Λ * ((3 : ℝ) ^ (s * (j : ℝ) / 8)) ^ Λ)) := by
        rw [← hden]
        gcongr
        exact hP.trans (ENNReal.div_le_div_right hnumE _)
    _ = ENNReal.ofReal (((ns : ℝ) + 1) * ((9 : ℝ) ^ (d * (j + 1)) * (16 : ℝ) ^ (j + 1) /
          (6 ^ Λ * ((3 : ℝ) ^ (s * (j : ℝ) / 8)) ^ Λ))) := by
        have e1 : ((ns : ℝ≥0∞) + 1) = ENNReal.ofReal ((ns : ℝ) + 1) := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one]
        rw [e1, ← ENNReal.ofReal_div_of_pos hdpos, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (Real.exp (-R * ((j + 1 : ℕ) : ℝ)) / 6) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ hdpos]
        push_cast
        linarith [hnj]

end Paper
