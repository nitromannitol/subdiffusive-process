module

public import SubdiffusiveProcess.Paper.Foundations.PrefixPrawMoment

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Pad tests from layer-adapted banks (deterministic part)

For a potential sample `g`, a level `n` and a centre `y`: if at every discount depth `j` each
layer-adapted bank of the layers `n-j, …, n+j` (at the cube level `n+1+j`) is at most
`3^{sj/8}/(2j+1)`, the field score formula of `primitive_scores` is at most `1`; if at every
depth `j` the product-window bank is at most `6·3^{sj/8}` and the tail-layer banks satisfy
`λ_{n,j,n+j+l} B_{n+j+l} ≤ 2^{-(l+1)} (1 + sj/8)`, the product score formula is at most `12`.
Nothing probabilistic is claimed here.
-/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ}

theorem aux_lfgc_fp_det_potentialField_translate_zero (g : PotentialField d) :
    PotentialField.translate 0 g = g :=
  PotentialField.ext (fun x => by rw [PotentialField.translate_apply, add_zero])

theorem aux_lfgc_fp_det_bank_maxObs_eq (i n : ℕ) (z : Vec d) (g : PotentialSample d) :
    Paper.aux_prefix_bank_maxObs i n z g = Paper.aux_prefix_praw_bank i n z g := by
  unfold Paper.aux_prefix_bank_maxObs Paper.aux_prefix_praw_bank Paper.aux_psf_cellObs
    Paper.aux_prefix_praw_obs Paper.aux_prefix_praw_cellField
  simp only [aux_lfgc_fp_det_potentialField_translate_zero, pow_zero, one_mul]

/-- Every value-plus-gradient observation on the cube is bounded by the layer bank. -/
theorem aux_lfgc_fp_det_obs_le_bank (i n : ℕ) (hin : i ≤ n) (z x : Vec d) (g : PotentialSample d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    |g i x| + (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (g i) x) ≤
      Paper.aux_prefix_praw_bank i n z g := by
  rw [← aux_lfgc_fp_det_bank_maxObs_eq]
  exact Paper.aux_prefix_bank_le_maxObs i n hin z x g hx

theorem aux_lfgc_fp_det_card_Icc_sub_add_le (n j : ℕ) :
    ((Finset.Icc (n - j) (n + j)).card : ℝ) ≤ 2 * j + 1 := by
  rw [Nat.card_Icc]
  have : n + j + 1 - (n - j) ≤ 2 * j + 1 := by omega
  exact_mod_cast this

/-- The field score formula is at most one under the depth-wise layer bank bounds. -/
theorem aux_lfgc_fp_det_fsc_le_one (s : ℝ) (g : PotentialSample d) (n : ℕ) (y : Vec d)
    (hF : ∀ j : ℕ, ∀ i ∈ Finset.Icc (n - j) (n + j),
      Paper.aux_prefix_praw_bank i (n + 1 + j) y g ≤ (3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1)) :
    sSup {v : ℝ≥0∞ | ∃ j : ℕ,
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        ∑ i ∈ Finset.Icc (n - j) (n + j),
          sSup {w : ℝ≥0∞ | ∃ x : Vec d, x ∈ translatedCube d (n + 1 + j) y ∧
            w = ENNReal.ofReal |(|g i x| + (3 : ℝ) ^ (i : ℝ) *
              Homogenization.euclideanNorm (shellGradient (g i) x))|}} ≤ 1 := by
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  have hcast : ((n : ℤ) + 1 + (j : ℤ)) = (((n + 1 + j : ℕ)) : ℤ) := by push_cast; ring
  have hterm : ∀ i ∈ Finset.Icc (n - j) (n + j),
      sSup {w : ℝ≥0∞ | ∃ x : Vec d, x ∈ translatedCube d (n + 1 + j) y ∧
        w = ENNReal.ofReal |(|g i x| + (3 : ℝ) ^ (i : ℝ) *
          Homogenization.euclideanNorm (shellGradient (g i) x))|} ≤
        ENNReal.ofReal ((3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1)) := by
    intro i hi
    refine sSup_le ?_
    rintro w ⟨x, hx, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    have hin : i ≤ n + 1 + j := by have := (Finset.mem_Icc.mp hi).2; omega
    rw [hcast] at hx
    have hb := aux_lfgc_fp_det_obs_le_bank i (n + 1 + j) hin y x g hx
    have hnn : 0 ≤ |g i x| + (3 : ℝ) ^ (i : ℝ) *
        Homogenization.euclideanNorm (shellGradient (g i) x) := by
      have := Real.sqrt_nonneg (Homogenization.vecNormSq (shellGradient (g i) x))
      positivity
    rw [abs_of_nonneg hnn, Real.rpow_natCast]
    exact hb.trans (hF j i hi)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1) := by positivity
  have hcard : ((Finset.Icc (n - j) (n + j)).card : ℝ≥0∞) *
      ENNReal.ofReal ((3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (s * (j : ℝ) / 8)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := aux_lfgc_fp_det_card_Icc_sub_add_le n j
    have h2 : (0 : ℝ) < 2 * j + 1 := by positivity
    calc ((Finset.Icc (n - j) (n + j)).card : ℝ) * ((3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1))
        ≤ (2 * j + 1) * ((3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1)) :=
          mul_le_mul_of_nonneg_right h1 hpos
      _ = (3 : ℝ) ^ (s * (j : ℝ) / 8) := by field_simp
  calc ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      ∑ i ∈ Finset.Icc (n - j) (n + j),
        sSup {w : ℝ≥0∞ | ∃ x : Vec d, x ∈ translatedCube d (n + 1 + j) y ∧
          w = ENNReal.ofReal |(|g i x| + (3 : ℝ) ^ (i : ℝ) *
            Homogenization.euclideanNorm (shellGradient (g i) x))|}
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ENNReal.ofReal ((3 : ℝ) ^ (s * (j : ℝ) / 8)) := by
        gcongr
        exact hsum.trans hcard
    _ = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by norm_num), neg_add_cancel,
          Real.rpow_zero, ENNReal.ofReal_one]

theorem aux_lfgc_fp_det_one_le_log_six : (1 : ℝ) ≤ Real.log 6 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem aux_lfgc_fp_det_one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- The tail product bank is at most `6·3^{sj/8}` under geometric tail-layer bounds. -/
theorem aux_lfgc_fp_det_bmaj_le (s : ℝ) (hs : 0 ≤ s) (n j : ℕ) (y : Vec d) (g : PotentialSample d)
    (hB : ∀ l : ℕ, Paper.aux_psf_lam n j (n + j + l) *
      Paper.aux_prefix_praw_bank (n + j + l) (n + 1 + j) y g ≤
        (1 / 2 : ℝ) ^ (l + 1) * (1 + s * (j : ℝ) / 8)) :
    Paper.aux_prefix_praw_Bmaj n j y g ≤ ENNReal.ofReal (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8)) := by
  refine iSup_le fun K => ENNReal.ofReal_le_ofReal ?_
  have hA : (0 : ℝ) ≤ 1 + s * (j : ℝ) / 8 := by positivity
  have hsum : ∑ i ∈ Finset.Icc (n + j) (n + j + K),
      Paper.aux_psf_lam n j i * Paper.aux_prefix_praw_bank i (n + 1 + j) y g ≤
        1 + s * (j : ℝ) / 8 := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    have hlen : Order.succ (n + j + K) - (n + j) = K + 1 := by
      change n + j + K + 1 - (n + j) = K + 1
      omega
    rw [hlen]
    calc ∑ l ∈ Finset.range (K + 1), Paper.aux_psf_lam n j (n + j + l) *
          Paper.aux_prefix_praw_bank (n + j + l) (n + 1 + j) y g
        ≤ ∑ l ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ (l + 1) * (1 + s * (j : ℝ) / 8) :=
          Finset.sum_le_sum fun l _ => hB l
      _ = (1 / 2 : ℝ) * (∑ l ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ l) *
            (1 + s * (j : ℝ) / 8) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
      _ ≤ (1 / 2 : ℝ) * 2 * (1 + s * (j : ℝ) / 8) := by
          have := sum_geometric_two_le (K + 1)
          gcongr
      _ = 1 + s * (j : ℝ) / 8 := by ring
  have hlog : 1 + s * (j : ℝ) / 8 ≤ Real.log (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8)) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by norm_num)]
    have h6 := aux_lfgc_fp_det_one_le_log_six
    have h3 := aux_lfgc_fp_det_one_le_log_three
    have hj : (0 : ℝ) ≤ s * (j : ℝ) / 8 := by positivity
    nlinarith
  calc Real.exp (∑ i ∈ Finset.Icc (n + j) (n + j + K),
        Paper.aux_psf_lam n j i * Paper.aux_prefix_praw_bank i (n + 1 + j) y g)
      ≤ Real.exp (Real.log (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8))) :=
        Real.exp_le_exp.mpr (hsum.trans hlog)
    _ = 6 * (3 : ℝ) ^ (s * (j : ℝ) / 8) := Real.exp_log (by positivity)

/-- The product score formula is at most twelve under the depth-wise bank bounds. -/
theorem lfgc_fp_det (hd : (1 : ℝ) ≤ (d : ℝ)) (s : ℝ) (g : PotentialSample d) (n : ℕ)
    (y : Vec d)
    (hA : ∀ j : ℕ, Paper.aux_prefix_praw_Amaj n j y g ≤
      ENNReal.ofReal (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8)))
    (hB : ∀ j : ℕ, Paper.aux_prefix_praw_Bmaj n j y g ≤
      ENNReal.ofReal (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8))) :
    sSup {v : ℝ≥0∞ | ∃ j : ℕ,
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        sSup {w : ℝ≥0∞ | ∃ x : Vec d, x ∈ translatedCube d (n + 1 + j) y ∧
          w = (∏ i ∈ Finset.Icc (n - j) (n + j),
                ENNReal.ofReal (Real.exp |g i x|)) +
              sSup {u : ℝ≥0∞ | ∃ K : ℕ,
                u = ∏ i ∈ Finset.Icc (n + j) (n + j + K),
                  ENNReal.ofReal (Real.exp (4 * |g i x - g i y|))}}} ≤ 12 := by
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  have hP := Paper.aux_prefix_praw_Pterm_le hd n j y g
  have hT : Paper.aux_prefix_praw_Amaj n j y g + Paper.aux_prefix_praw_Bmaj n j y g ≤
      ENNReal.ofReal (12 * (3 : ℝ) ^ (s * (j : ℝ) / 8)) := by
    have h12 : (12 : ℝ) * (3 : ℝ) ^ (s * (j : ℝ) / 8) =
        6 * (3 : ℝ) ^ (s * (j : ℝ) / 8) + 6 * (3 : ℝ) ^ (s * (j : ℝ) / 8) := by ring
    rw [h12, ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add (hA j) (hB j)
  calc ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      sSup {w : ℝ≥0∞ | ∃ x : Vec d, x ∈ translatedCube d (n + 1 + j) y ∧
        w = (∏ i ∈ Finset.Icc (n - j) (n + j),
              ENNReal.ofReal (Real.exp |g i x|)) +
            sSup {u : ℝ≥0∞ | ∃ K : ℕ,
              u = ∏ i ∈ Finset.Icc (n + j) (n + j + K),
                ENNReal.ofReal (Real.exp (4 * |g i x - g i y|))}}
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ENNReal.ofReal (12 * (3 : ℝ) ^ (s * (j : ℝ) / 8)) := by
        gcongr
        exact hP.trans hT
    _ = 12 := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        rw [show (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * (12 * (3 : ℝ) ^ (s * (j : ℝ) / 8)) =
          12 * ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * (3 : ℝ) ^ (s * (j : ℝ) / 8)) by ring]
        rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero, mul_one]
        norm_num

end Paper
