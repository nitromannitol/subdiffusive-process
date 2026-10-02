import SubdiffusiveProcess.Paper.Foundations.PrefixPrawMoment
import SubdiffusiveProcess.PrefixPrawSeries

/-!
# Cutoff-uniform `R`-th moment of the literal product score `Psc`

`aux_prefix_praw_PscF s m z omega` is, verbatim, the right-hand side of clause (3) of
`primitive_scores`.  Its `R`-th moment under `M.P` is bounded by the explicit series
`∑ j, aux_prefix_praw_term d s R σ C_B j`, which depends on neither the cutoff depth `m`
nor the centre `z`, and which is finite once `R ≥ 1`, `32 (d+1) ≤ s R` and `16 R σ² ≤ s`.
-/

noncomputable section

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper

variable {d : ℕ}

/-- The literal `primitive_scores` product score (clause (3)). -/
def aux_prefix_praw_PscF (s : ℝ) (m : ℕ) (z : Vec d) (omega : PotentialSample d) : ℝ≥0∞ :=
  sSup {v : ENNReal | ∃ j : ℕ,
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
        w = (∏ i ∈ Finset.Icc (m - j) (m + j),
              ENNReal.ofReal (Real.exp |omega i x|)) +
            sSup {u : ENNReal | ∃ K : ℕ,
              u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}}}

/-- The tail constant `C_B = (7^d * 2 e^{θ²σ²/4})^{9R/θ}` with `θ = 6R+1`. -/
def aux_prefix_praw_CB (M : GMCModel d) (R : ℝ) : ℝ :=
  ((7 : ℝ) ^ d * (Real.exp ((6 * R + 1) ^ 2 * aux_psf_sigma M ^ 2 / 4) * 2)) ^
    (9 * R / (6 * R + 1))

theorem aux_prefix_praw_CB_nonneg (M : GMCModel d) (R : ℝ) : 0 ≤ aux_prefix_praw_CB M R := by
  unfold aux_prefix_praw_CB
  positivity

/-- The tail bank moment in real form. -/
theorem aux_prefix_praw_Bmaj_rpow_lintegral_CB (M : GMCModel d) (m j : ℕ) (z : Vec d)
    (R : ℝ) (hR : 0 < R) :
    (∫⁻ omega : PotentialSample d, (aux_prefix_praw_Bmaj m j z omega) ^ R ∂M.P.toMeasure) ≤
      ENNReal.ofReal (aux_prefix_praw_CB M R) := by
  refine (aux_prefix_praw_Bmaj_rpow_lintegral M m j z R (6 * R + 1) hR (by linarith)).trans
    (le_of_eq ?_)
  have hth : 0 ≤ 9 * R / (6 * R + 1) := by positivity
  unfold aux_prefix_praw_CB
  rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hth]
  congr 1
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  norm_num

/-- The product-window bank moment in real form, with the cutoff-free cardinal. -/
theorem aux_prefix_praw_Amaj_rpow_lintegral_real (M : GMCModel d) (m j : ℕ) (z : Vec d)
    (R : ℝ) :
    (∫⁻ omega : PotentialSample d, (aux_prefix_praw_Amaj m j z omega) ^ R ∂M.P.toMeasure) ≤
      ENNReal.ofReal ((((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) *
        (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4) * 2) ^ (2 * j + 1)) := by
  refine (aux_prefix_praw_Amaj_rpow_lintegral M m j z R).trans ?_
  have hE1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2 := by
    have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4)) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
    have := mul_le_mul' h (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa using this
  have hcard : ((aux_psf_cells d (m + 1 + j - (m - j))).card : ℝ≥0∞) ≤
      (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ≥0∞) := by
    rw [aux_psf_cells_card]
    have hgap : m + 1 + j - (m - j) ≤ 2 * j + 1 := by omega
    have h3 : 3 ^ (m + 1 + j - (m - j)) ≤ 3 ^ (2 * j + 1) := Nat.pow_le_pow_right (by norm_num) hgap
    exact_mod_cast Nat.pow_le_pow_left (by omega) d
  have hW : (Finset.Icc (m - j) (m + j)).card ≤ 2 * j + 1 := by
    rw [Nat.card_Icc]; omega
  calc ((aux_psf_cells d (m + 1 + j - (m - j))).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^
          ((Finset.Icc (m - j) (m + j)).card) ≤
      (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^ (2 * j + 1) := by
        exact mul_le_mul' hcard (pow_le_pow_right₀ hE1 hW)
    _ = _ := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (Real.exp_nonneg _)]
        norm_num

/-- Pointwise: the `R`-th power of the product score is dominated by the discounted sum
of the two banks' powers. -/
theorem aux_prefix_praw_PscF_rpow_le (hd : (1 : ℝ) ≤ (d : ℝ)) (s R : ℝ) (hR : 0 < R)
    (m : ℕ) (z : Vec d) (omega : PotentialSample d) :
    (aux_prefix_praw_PscF s m z omega) ^ R ≤
      ∑' j : ℕ, (ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        (aux_prefix_praw_Amaj m j z omega + aux_prefix_praw_Bmaj m j z omega)) ^ R := by
  set T : ℝ≥0∞ := ∑' j : ℕ, (ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
    (aux_prefix_praw_Amaj m j z omega + aux_prefix_praw_Bmaj m j z omega)) ^ R with hT
  have hsup : aux_prefix_praw_PscF s m z omega ≤ T ^ (1 / R) := by
    refine sSup_le ?_
    rintro v ⟨j, rfl⟩
    have hPt := aux_prefix_praw_Pterm_le hd m j z omega
    have h1 : ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
          w = (∏ i ∈ Finset.Icc (m - j) (m + j),
                ENNReal.ofReal (Real.exp |omega i x|)) +
              sSup {u : ENNReal | ∃ K : ℕ,
                u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                  ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}} ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          (aux_prefix_praw_Amaj m j z omega + aux_prefix_praw_Bmaj m j z omega) := by
      gcongr
    refine h1.trans ?_
    set a : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      (aux_prefix_praw_Amaj m j z omega + aux_prefix_praw_Bmaj m j z omega) with ha
    have hle : a ^ R ≤ T := ENNReal.le_tsum (f := fun j : ℕ =>
      (ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        (aux_prefix_praw_Amaj m j z omega + aux_prefix_praw_Bmaj m j z omega)) ^ R) j
    have h := ENNReal.rpow_le_rpow hle (by positivity : 0 ≤ 1 / R)
    simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hR.ne', ENNReal.rpow_one] using h
  have h := ENNReal.rpow_le_rpow hsup hR.le
  simpa only [← ENNReal.rpow_mul, one_div_mul_cancel hR.ne', ENNReal.rpow_one] using h

/-- The `ENNReal` form of one series term. -/
theorem aux_prefix_praw_ofReal_term (M : GMCModel d) (s R : ℝ) (hR : 1 ≤ R) (j : ℕ) :
    ENNReal.ofReal (aux_prefix_praw_term d s R (aux_psf_sigma M) (aux_prefix_praw_CB M R) j) =
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) ^ R *
        (2 ^ (R - 1) *
          (ENNReal.ofReal ((((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) *
              (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4) * 2) ^ (2 * j + 1)) +
            ENNReal.ofReal (aux_prefix_praw_CB M R))) := by
  have hCB := aux_prefix_praw_CB_nonneg M R
  have hA : (0 : ℝ) ≤ (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) *
      (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4) * 2) ^ (2 * j + 1) := by positivity
  unfold aux_prefix_praw_term
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) := by positivity
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add hA hCB,
    ← ENNReal.ofReal_rpow_of_nonneg (x := (3 : ℝ) ^ (-(s * (j : ℝ) / 8))) (p := R) h3
      (by linarith),
    ← ENNReal.ofReal_rpow_of_nonneg (x := (2 : ℝ)) (p := R - 1) (by norm_num) (by linarith)]
  norm_num

/-- **Cutoff-uniform `R`-th moment of the literal product score.** For every `R ≥ 1`, the
bound is the same explicit series for all cutoff depths `m` and centres `z`. -/
theorem aux_prefix_praw_PscF_rpow_lintegral_le (hd : (1 : ℝ) ≤ (d : ℝ)) (M : GMCModel d)
    (s R : ℝ) (hR : 1 ≤ R) (m : ℕ) (z : Vec d) :
    (∫⁻ omega : PotentialSample d, (aux_prefix_praw_PscF s m z omega) ^ R ∂M.P.toMeasure) ≤
      ∑' j : ℕ, ENNReal.ofReal
        (aux_prefix_praw_term d s R (aux_psf_sigma M) (aux_prefix_praw_CB M R) j) := by
  have hR0 : 0 < R := by linarith
  refine (lintegral_mono (fun omega => aux_prefix_praw_PscF_rpow_le hd s R hR0 m z omega)).trans ?_
  have hmeas : ∀ j : ℕ, Measurable (fun omega : PotentialSample d =>
      (ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        (aux_prefix_praw_Amaj m j z omega + aux_prefix_praw_Bmaj m j z omega)) ^ R) := by
    intro j
    exact (((aux_prefix_praw_Amaj_measurable m j z).add
      (aux_prefix_praw_Bmaj_measurable m j z)).const_mul _).pow_const R
  rw [lintegral_tsum (fun j => (hmeas j).aemeasurable)]
  refine ENNReal.tsum_le_tsum (fun j => ?_)
  rw [aux_prefix_praw_ofReal_term M s R hR j]
  have hsplit : ∀ omega : PotentialSample d,
      (ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        (aux_prefix_praw_Amaj m j z omega + aux_prefix_praw_Bmaj m j z omega)) ^ R ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) ^ R *
        (2 ^ (R - 1) * ((aux_prefix_praw_Amaj m j z omega) ^ R +
          (aux_prefix_praw_Bmaj m j z omega) ^ R)) := by
    intro omega
    rw [ENNReal.mul_rpow_of_nonneg _ _ hR0.le]
    gcongr
    exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hR
  refine (lintegral_mono hsplit).trans ?_
  rw [lintegral_const_mul _ (((aux_prefix_praw_Amaj_measurable m j z).pow_const R).add
      ((aux_prefix_praw_Bmaj_measurable m j z).pow_const R) |>.const_mul _),
    lintegral_const_mul _ (((aux_prefix_praw_Amaj_measurable m j z).pow_const R).add
      ((aux_prefix_praw_Bmaj_measurable m j z).pow_const R)),
    lintegral_add_left ((aux_prefix_praw_Amaj_measurable m j z).pow_const R)]
  gcongr
  · exact aux_prefix_praw_Amaj_rpow_lintegral_real M m j z R
  · exact aux_prefix_praw_Bmaj_rpow_lintegral_CB M m j z R hR0

/-- Under the exponent/disorder budget the uniform bound is finite. -/
theorem aux_prefix_praw_series_ne_top (M : GMCModel d) (s R : ℝ) (hs : 0 < s) (hR : 1 ≤ R)
    (hRs : 32 * ((d : ℝ) + 1) ≤ s * R) (hσ : 16 * R * aux_psf_sigma M ^ 2 ≤ s) :
    (∑' j : ℕ, ENNReal.ofReal
      (aux_prefix_praw_term d s R (aux_psf_sigma M) (aux_prefix_praw_CB M R) j)) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (aux_prefix_praw_term_nonneg d s R _ _ (aux_prefix_praw_CB_nonneg M R))
    (aux_prefix_praw_term_summable d s R _ _ hs hR hRs hσ (aux_prefix_praw_CB_nonneg M R))]
  exact ENNReal.ofReal_ne_top

end Paper
