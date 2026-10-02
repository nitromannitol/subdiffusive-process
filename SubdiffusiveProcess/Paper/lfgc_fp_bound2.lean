import SubdiffusiveProcess.Paper.lfgc_fp_bound

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Pad-test pieces: the tail-layer banks of one window

For the window index `h`, the tail-layer banks `(j', l)` with `j' + l + 1 = h` exceed the
thresholds `aux_lfgc_fp_bound2_tB s j' l = (3/2)^l (1 + s j'/8)/12` with total probability at most
`e^{-R h}/(6 (ns+1))` once the bank scale is small.  `λ_{n,j,n+j+l} aux_lfgc_fp_bound2_tB s j l` equals the
geometric budget `2^{-(l+1)} (1 + sj/8)` of `bmaj_le`.
-/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The tail-layer threshold. -/
noncomputable def aux_lfgc_fp_bound2_tB (s : ℝ) (j l : ℕ) : ℝ := (3 / 2 : ℝ) ^ l * (1 + s * (j : ℝ) / 8) / 12

theorem aux_lfgc_fp_bound2_lam_mul_tB (s : ℝ) (n j l : ℕ) :
    Paper.aux_psf_lam n j (n + j + l) * aux_lfgc_fp_bound2_tB s j l = (1 / 2 : ℝ) ^ (l + 1) * (1 + s * (j : ℝ) / 8) := by
  unfold Paper.aux_psf_lam aux_lfgc_fp_bound2_tB
  have h3 : (3 : ℝ) ^ (n + 1 + j) = 3 * (3 : ℝ) ^ (n + j) := by
    rw [show n + 1 + j = (n + j) + 1 by ring, pow_succ]; ring
  have h3' : (3 : ℝ) ^ (n + j + l) = (3 : ℝ) ^ (n + j) * (3 : ℝ) ^ l := pow_add _ _ _
  rw [h3, h3', div_pow, one_div_pow, pow_succ]
  have hp : (0 : ℝ) < (3 : ℝ) ^ (n + j) := by positivity
  have hq : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  field_simp
  ring

/-- The tail-layer pieces of window `h`. -/
theorem lfgc_fp_bound2 (M : GMCModel d) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (ns : ℕ) {R : ℝ}
    (hsmall : Real.log (6 * (2 * 7 ^ d * ((ns : ℝ) + 1))) + Real.log 2 + R ≤
      (s / 96 / Paper.aux_psf_sigma M) ^ 2)
    (N n h : ℕ) (hh : 1 ≤ h) (y : Vec d) :
    ((ns : ℝ≥0∞) + 1) * (chaosSampleLaw M).toMeasure
      (⋃ l ∈ Finset.range h,
        aux_lfgc_fp_events_bankEv N (n + (h - 1 - l) + l) (n + 1 + (h - 1 - l)) y (aux_lfgc_fp_bound2_tB s (h - 1 - l) l)) ≤
      ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 6) := by
  have hσ := Paper.aux_psf_sigma_pos M
  have hc : 0 < s / 96 := by positivity
  set g := Real.exp (-(s / 96 * (h : ℝ) / Paper.aux_psf_sigma M) ^ 2) with hg
  have hterm : ∀ l ∈ Finset.range h,
      (chaosSampleLaw M).toMeasure
        (aux_lfgc_fp_events_bankEv N (n + (h - 1 - l) + l) (n + 1 + (h - 1 - l)) y (aux_lfgc_fp_bound2_tB s (h - 1 - l) l)) ≤
        ENNReal.ofReal ((7 : ℝ) ^ d * 2 * g) := by
    intro l hl
    have hlh : l < h := Finset.mem_range.mp hl
    have ht := bThreshold_ge hs hs1 (h - 1 - l) l
    have hjl : ((h - 1 - l : ℕ) : ℝ) + l + 1 = h := by
      have : h - 1 - l + l + 1 = h := by omega
      exact_mod_cast this
    rw [hjl] at ht
    have ht0 : 0 ≤ aux_lfgc_fp_bound2_tB s (h - 1 - l) l := le_trans (by positivity) ht
    refine (lfgc_fp_events M N _ _ y ht0).trans ?_
    have hcard := aux_lfgc_fp_bound_cells_card_le_seven (d := d)
      (n + 1 + (h - 1 - l) - (n + (h - 1 - l) + l)) (by omega)
    have hexp : Real.exp (-(aux_lfgc_fp_bound2_tB s (h - 1 - l) l / Paper.aux_psf_sigma M) ^ 2) ≤ g := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : s / 96 * (h : ℝ) / Paper.aux_psf_sigma M ≤
          aux_lfgc_fp_bound2_tB s (h - 1 - l) l / Paper.aux_psf_sigma M :=
        div_le_div_of_nonneg_right ht hσ.le
      have h2 : 0 ≤ s / 96 * (h : ℝ) / Paper.aux_psf_sigma M := by positivity
      nlinarith
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    gcongr
    · rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hcard
    · norm_num
  have hU := aux_lfgc_fp_bound_measure_biUnion_le_card (chaosSampleLaw M).toMeasure _ _ hterm
  rw [Finset.card_range] at hU
  have hmain := gauss_tail_le hc hσ (K := 2 * 7 ^ d * ((ns : ℝ) + 1)) (Q := 2) (R := R)
    (by
      have h7 : (1 : ℝ) ≤ 7 ^ d := one_le_pow₀ (by norm_num)
      have hns : (0 : ℝ) ≤ ns := Nat.cast_nonneg ns
      nlinarith)
    (by norm_num) hsmall hh (t := s / 96 * (h : ℝ)) le_rfl
  have e1 : ((ns : ℝ≥0∞) + 1) = ENNReal.ofReal ((ns : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  have e2 : ((h : ℕ) : ℝ≥0∞) = ENNReal.ofReal (h : ℝ) := (ENNReal.ofReal_natCast _).symm
  calc ((ns : ℝ≥0∞) + 1) * (chaosSampleLaw M).toMeasure
        (⋃ l ∈ Finset.range h,
          aux_lfgc_fp_events_bankEv N (n + (h - 1 - l) + l) (n + 1 + (h - 1 - l)) y (aux_lfgc_fp_bound2_tB s (h - 1 - l) l))
      ≤ ((ns : ℝ≥0∞) + 1) * ((h : ℝ≥0∞) * ENNReal.ofReal ((7 : ℝ) ^ d * 2 * g)) := by gcongr
    _ = ENNReal.ofReal (((ns : ℝ) + 1) * ((h : ℝ) * ((7 : ℝ) ^ d * 2 * g))) := by
        rw [e1, e2, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 6) := by
        refine ENNReal.ofReal_le_ofReal (le_trans ?_ hmain)
        have h2h : (h : ℝ) ≤ (2 : ℝ) ^ h := by
          have := Nat.lt_two_pow_self (n := h)
          exact_mod_cast this.le
        have hg0 : 0 ≤ g := (Real.exp_pos _).le
        have h7 : (0 : ℝ) ≤ 7 ^ d := by positivity
        have hns : (0 : ℝ) ≤ ns := Nat.cast_nonneg ns
        calc ((ns : ℝ) + 1) * ((h : ℝ) * ((7 : ℝ) ^ d * 2 * g))
            ≤ ((ns : ℝ) + 1) * ((2 : ℝ) ^ h * ((7 : ℝ) ^ d * 2 * g)) := by gcongr
          _ = 2 * 7 ^ d * ((ns : ℝ) + 1) * 2 ^ h * g := by ring

end Paper
