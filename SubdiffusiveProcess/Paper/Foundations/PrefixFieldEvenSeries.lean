import SubdiffusiveProcess.Paper.Foundations.PrefixFieldNumeric

noncomputable section

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess

namespace Paper

noncomputable def prefix_even_series_bound {d : ℕ} (M : GMCModel d)
    (s : ℝ) (q j : ℕ) : ℝ :=
  (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
    (2 * aux_psf_sigma M * ((q : ℝ) + 1 + prefix_log_card d j))

theorem prefix_even_series_bound_nonneg {d : ℕ} (M : GMCModel d)
    (s : ℝ) (q j : ℕ) : 0 ≤ prefix_even_series_bound M s q j := by
  unfold prefix_even_series_bound
  have hL := prefix_log_card_nonneg d j
  have hσ := (aux_psf_sigma_pos M).le
  positivity

theorem prefix_even_series_bound_summable {d : ℕ} (M : GMCModel d)
    (s : ℝ) (hs : 0 < s) (q : ℕ) :
    Summable (fun j : ℕ => prefix_even_series_bound M s q j) := by
  set r : ℝ := (3 : ℝ) ^ (-(s / 8)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hrn : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hrj : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) = r ^ j := by
    intro j
    rw [hr, ← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 8))) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrn
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hrn
  have hlin : Summable (fun j : ℕ =>
      ((2 * j + 1 : ℕ) : ℝ) * r ^ j) := by
    refine ((h1.mul_left 2).add h0).congr ?_
    intro j
    push_cast
    ring
  have hq : Summable (fun j : ℕ =>
      (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
        (2 * aux_psf_sigma M * (q : ℝ))) := by
    have h := hlin.mul_left (2 * aux_psf_sigma M * (q : ℝ))
    exact h.congr (by
      intro j
      rw [hrj]
      ring)
  have hsum := (prefix_L2_series_bound_summable M s hs).add hq
  exact hsum.congr (by
    intro j
    dsimp [prefix_even_series_bound, prefix_L2_series_bound]
    ring)


end Paper
