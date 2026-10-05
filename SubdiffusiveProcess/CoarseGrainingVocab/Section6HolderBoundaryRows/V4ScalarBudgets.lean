module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.IterationApplied

@[expose] public section

/-!
# Scalar budgets for the v4 boundary Holder recurrence

The v4 excess-decay statement changes the contraction price from `s⁻³ᐟ²` to
`s⁻²`.  At the fixed scale `s = 1/4`, doubling the old contraction constant
exactly pays this change.  The second lemma is the parameter absorption used
for the accumulated datum-mean defect.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

noncomputable section

/-- At `s = 1/4`, the v4 contraction follows from the v3-shaped contraction
with the step constant doubled. -/
theorem v4_contraction_of_doubled_v3
    {C a b epsilon T : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hold : 2 * C * (a + (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * b * epsilon) ≤ T) :
    C * (a + (1 / 4 : ℝ) ^ (-2 : ℝ) * b * epsilon) ≤ T := by
  have hp : (1 / 4 : ℝ) ^ (-2 : ℝ) =
      2 * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    rw [show (-3 / 2 : ℝ) = (-3 : ℝ) / 2 by ring,
      Real.rpow_div_two_eq_sqrt _ (by positivity)]
    norm_num
  rw [hp]
  nlinarith only [hold, hC, ha]

/-- The raised stopping budget retains the printed `(1-alpha) * gap` factor.
The harmless shift from `n` to `n+1` cancels exactly with the terminal `+1`.
-/
theorem raised_lambda_gap_absorption
    {C1 alpha m n : ℝ} (hC1 : 1 ≤ C1) (halpha : alpha ≤ 1)
    (hgap : 0 ≤ m - n) :
    C1⁻¹ * (1 - alpha) * (m - (n + 1) + 1) ≤
      (1 - alpha) * (m - n) := by
  have hC1pos : 0 < C1 := lt_of_lt_of_le zero_lt_one hC1
  have hinv1 : C1⁻¹ ≤ 1 := by rw [inv_le_one₀ hC1pos]; exact hC1
  have hinv0 : 0 ≤ C1⁻¹ := inv_nonneg.mpr hC1pos.le
  have ha0 : 0 ≤ 1 - alpha := by linarith
  have hprod : 0 ≤ (1 - alpha) * (m - n) := mul_nonneg ha0 hgap
  ring_nf
  nlinarith

theorem component_one_le_sum5 {a b c d e : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    a ≤ a + (b + c) + d + e := by linarith

theorem component_two_le_sum5 {a b c d e : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    b ≤ a + (b + c) + d + e := by linarith

theorem component_three_le_sum5 {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (he : 0 ≤ e) :
    c ≤ a + (b + c) + d + e := by linarith

theorem component_four_le_sum5 {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e) :
    d ≤ a + (b + c) + d + e := by linarith

theorem component_five_le_sum5 {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    e ≤ a + (b + c) + d + e := by linarith

/-- Simultaneous absorption of the forcing, datum-mean, and datum-seminorm
parts of the stopped defect.  The indicator is kept explicit so the result
vanishes on interior windows. -/
theorem boundary_defect_threeTerm_absorption
    {P Pmax R Rmax D Af F Am G H Ab Q S Fr B I C outer : ℝ}
    (hP0 : 0 ≤ P) (hP : P ≤ Pmax) (hPmax : 0 ≤ Pmax)
    (hR0 : 0 ≤ R) (hR : R ≤ Rmax)
    (hD0 : 0 ≤ D) (hD : D ≤ Af * F + Am * G * H * B + Ab * Q * S * B)
    (hAf : 0 ≤ Af) (hF : 0 ≤ F) (hAm : 0 ≤ Am) (hG : 0 ≤ G)
    (hH : 0 ≤ H) (hAb : 0 ≤ Ab) (hQ : 0 ≤ Q) (hS : 0 ≤ S)
    (hB : 0 ≤ B) (hBI : B ≤ I) (hI : 0 ≤ I)
    (hSFrac : S ≤ Fr)
    (houter : 0 < outer)
    (hcF : Pmax * (1 + Rmax) * Af * outer ≤ C)
    (hcM : Pmax * (1 + Rmax) * Am * outer ≤ C)
    (hcB : Pmax * (1 + Rmax) * Ab * outer ≤ C) :
    P * ((1 + R) * D) ≤
      (C * F + I * C * (G * H + Q * Fr)) / outer := by
  have hRmax0 : 0 ≤ Rmax := hR0.trans hR
  have hfac : P * (1 + R) ≤ Pmax * (1 + Rmax) := by
    exact mul_le_mul hP (by linarith) (by positivity) hPmax
  have hfac0 : 0 ≤ P * (1 + R) := mul_nonneg hP0 (by linarith)
  have hsum0 : 0 ≤ Af * F + Am * G * H * B + Ab * Q * S * B := by positivity
  have hC0 : 0 ≤ C := by
    have hleft : 0 ≤ Pmax * (1 + Rmax) * Af * outer := by positivity
    exact hleft.trans hcF
  have hCover0 : 0 ≤ C / outer := div_nonneg hC0 houter.le
  have hstart : P * ((1 + R) * D) ≤
      (Pmax * (1 + Rmax)) * (Af * F + Am * G * H * B + Ab * Q * S * B) := by
    calc
      P * ((1 + R) * D) = (P * (1 + R)) * D := by ring
      _ ≤ _ := mul_le_mul hfac hD hD0 (mul_nonneg hPmax (by linarith))
  have hFpart : (Pmax * (1 + Rmax)) * (Af * F) ≤ (C / outer) * F := by
    have hc : Pmax * (1 + Rmax) * Af ≤ C / outer := by
      rw [le_div_iff₀ houter]
      simpa only [mul_assoc] using hcF
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hF
  have hMpart : (Pmax * (1 + Rmax)) * (Am * G * H * B) ≤
      I * (C / outer) * (G * H) := by
    have hc : Pmax * (1 + Rmax) * Am ≤ C / outer := by
      rw [le_div_iff₀ houter]
      simpa only [mul_assoc] using hcM
    have hcoef := mul_le_mul hc hBI hB hCover0
    have hGH : 0 ≤ G * H := mul_nonneg hG hH
    have := mul_le_mul_of_nonneg_right hcoef hGH
    nlinarith only [this]
  have hBpart : (Pmax * (1 + Rmax)) * (Ab * Q * S * B) ≤
      I * (C / outer) * (Q * Fr) := by
    have hc : Pmax * (1 + Rmax) * Ab ≤ C / outer := by
      rw [le_div_iff₀ houter]
      simpa only [mul_assoc] using hcB
    have hcoef := mul_le_mul hc hBI hB hCover0
    have hQS : Q * S ≤ Q * Fr := mul_le_mul_of_nonneg_left hSFrac hQ
    have hcoef0 : 0 ≤ I * (C / outer) := mul_nonneg hI hCover0
    have h1 := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hQ hS)
    have h2 := mul_le_mul_of_nonneg_left hQS hcoef0
    nlinarith only [h1, h2]
  calc
    P * ((1 + R) * D) ≤ _ := hstart
    _ = (Pmax * (1 + Rmax)) * (Af * F) +
        (Pmax * (1 + Rmax)) * (Am * G * H * B) +
        (Pmax * (1 + Rmax)) * (Ab * Q * S * B) := by ring
    _ ≤ (C / outer) * F + I * (C / outer) * (G * H) +
        I * (C / outer) * (Q * Fr) := add_le_add (add_le_add hFpart hMpart) hBpart
    _ = (C * F + I * C * (G * H + Q * Fr)) / outer := by field_simp; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows
