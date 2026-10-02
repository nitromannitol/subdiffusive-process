import SubdiffusiveProcess.PrefixScores.Numerics

/-! Model-independent small-disorder arithmetic for the three good-scale tests. -/
namespace SubdiffusiveProcess.PrefixScores

lemma exists_badTest_budgets (s r e theta C1 C2 C3 B : ℝ)
    (hs : 0 < s) (hr : 0 < r) (he : 0 < e) (ht : 0 < theta)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3) (hB1 : 1 ≤ B) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ delta0 → delta ≤ 1 ∧
      C1 * r ^ (-6 : ℤ) * e⁻¹ ^ 2 * delta ^ 2 ≤ theta ∧
      C3 * r ^ (-3 : ℤ) * e⁻¹ ^ 2 * delta ^ 2 * |Real.log delta| ≤ theta ∧
      B ≤ r ^ 6 * e ^ 2 * theta / (C1 * delta ^ 2) ∧
      B ≤ r ^ 3 * e ^ 2 * theta / (C3 * delta ^ 2 * |Real.log delta|) ∧
      C2 * delta ^ 2 * B ≤ s ^ 2 * theta := by
  have hB : 0 < B := zero_lt_one.trans_le hB1
  set u1 := r ^ 6 * e ^ 2 * theta / (C1 * B) with hu1def
  set u2 := s ^ 2 * theta / (C2 * B) with hu2def
  set u3 := r ^ 3 * e ^ 2 * theta / (C3 * B) with hu3def
  have hu1 : 0 < u1 := by dsimp [u1]; positivity
  have hu2 : 0 < u2 := by dsimp [u2]; positivity
  have hu3 : 0 < u3 := by dsimp [u3]; positivity
  clear_value u1 u2 u3
  refine ⟨min (1 / 2) (min u1 (min u2 u3)), lt_min (by norm_num) (lt_min hu1 (lt_min hu2 hu3)), ?_⟩
  intro delta hd hdelta
  have hdHalf : delta ≤ 1 / 2 := hdelta.trans (min_le_left _ _)
  have hd1 : delta ≤ 1 := by linarith
  have hdsq : delta ^ 2 ≤ delta := by nlinarith
  have hdlog := delta_sq_log_le_self hd hd1
  have hdu1 : delta ≤ u1 := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdu2 : delta ≤ u2 := hdelta.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hdu3 : delta ≤ u3 := hdelta.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hb1 : C1 * delta ^ 2 * B ≤ r ^ 6 * e ^ 2 * theta := by
    calc
      _ ≤ C1 * u1 * B := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hdsq.trans hdu1) hC1.le) hB.le
      _ = r ^ 6 * e ^ 2 * theta := by rw [hu1def]; field_simp
  have hb2 : C2 * delta ^ 2 * B ≤ s ^ 2 * theta := by
    calc
      _ ≤ C2 * u2 * B := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hdsq.trans hdu2) hC2.le) hB.le
      _ = s ^ 2 * theta := by rw [hu2def]; field_simp
  have hb3 : C3 * (delta ^ 2 * |Real.log delta|) * B ≤ r ^ 3 * e ^ 2 * theta := by
    calc
      _ ≤ C3 * u3 * B := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hdlog.trans hdu3) hC3.le) hB.le
      _ = r ^ 3 * e ^ 2 * theta := by rw [hu3def]; field_simp
  have hlog : 0 < |Real.log delta| := abs_pos.mpr (Real.log_neg hd (by linarith)).ne
  have hbudget1 := density_budget 6 hr he
    ((le_mul_of_one_le_right (by positivity : 0 ≤ C1 * delta ^ 2) hB1).trans hb1)
  have hbudget3 := density_budget 3 hr he
    ((le_mul_of_one_le_right (by positivity : 0 ≤ C3 * (delta ^ 2 * |Real.log delta|)) hB1).trans hb3)
  refine ⟨hd1, hbudget1, ?_, rate_of_budget (by positivity) hb1, ?_, hb2⟩
  · simpa only [mul_assoc] using hbudget3
  · simpa only [mul_assoc] using rate_of_budget (by positivity) hb3

lemma linear_smallness_of_budget {c C s theta delta B : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < delta) (ht : 0 ≤ theta)
    (hcC : c ^ 2 ≤ C) (hB1 : 1 ≤ B) (hb : C * delta ^ 2 * B ≤ s ^ 2 * theta) :
    delta ≤ c⁻¹ * s * Real.sqrt theta := by
  have hC : 0 < C := (sq_pos_of_pos hc).trans_le hcC
  have h2 : (c * delta) ^ 2 ≤ (s * Real.sqrt theta) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht]
    exact (mul_le_mul_of_nonneg_right hcC (sq_nonneg delta)).trans
      ((le_mul_of_one_le_right (by positivity : 0 ≤ C * delta ^ 2) hB1).trans hb)
  have hlin : c * delta ≤ s * Real.sqrt theta := by
    nlinarith [mul_pos hc hd, mul_nonneg hs.le (Real.sqrt_nonneg theta)]
  have hdiv := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlin)
  convert hdiv using 1; ring

end SubdiffusiveProcess.PrefixScores
