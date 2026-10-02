import SubdiffusiveProcess.Frozen.Section6.Defs.GammaReg
import SubdiffusiveProcess.Frozen.Assumptions.GMCModel




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- `|log δ| ≤ 1/δ` for `0 < δ ≤ 1`. -/
theorem abs_log_le_inv {delta : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) :
    |Real.log delta| ≤ 1 / delta := by
  have hlog : Real.log delta ≤ 0 := Real.log_nonpos hd.le hd1
  rw [abs_of_nonpos hlog, ← Real.log_inv]
  have hinv : (0 : ℝ) < delta⁻¹ := inv_pos.2 hd
  have := Real.log_le_sub_one_of_pos hinv
  rw [one_div]
  linarith

/-- The key smallness estimate: `δ·√|log δ| ≤ √δ`. -/
theorem mul_sqrt_abs_log_le_sqrt {delta : ℝ} (hd : 0 < delta)
    (hd1 : delta ≤ 1) :
    delta * Real.sqrt |Real.log delta| ≤ Real.sqrt delta := by
  have hstep : Real.sqrt |Real.log delta| ≤ Real.sqrt (1 / delta) :=
    Real.sqrt_le_sqrt (abs_log_le_inv hd hd1)
  have hpos : 0 < Real.sqrt delta := Real.sqrt_pos.2 hd
  have hrw : delta * Real.sqrt (1 / delta) = Real.sqrt delta := by
    rw [one_div, Real.sqrt_inv, inv_eq_one_div, mul_one_div,
      div_eq_iff (ne_of_gt hpos)]
    exact (Real.mul_self_sqrt hd.le).symm
  calc delta * Real.sqrt |Real.log delta|
      ≤ delta * Real.sqrt (1 / delta) :=
        mul_le_mul_of_nonneg_left hstep hd.le
    _ = Real.sqrt delta := hrw

/-- **Premise 3, discharged.**  For `0 < δ ≤ 1/2` and `δ < 1/(4C₀²)`, the
regularity exponent lies strictly between `1/2` and `1`. -/
theorem gammaReg_mem_Ioo {C0 delta : ℝ} (hC0 : 0 < C0) (hd : 0 < delta)
    (hdhalf : delta ≤ 1 / 2) (hsmall : delta < 1 / (4 * C0 ^ 2)) :
    gammaReg C0 delta ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  have hd1 : delta ≤ 1 := by linarith
  have hsqrt : |Real.log delta| ^ (1 / 2 : ℝ) = Real.sqrt |Real.log delta| :=
    (Real.sqrt_eq_rpow _).symm
  -- The subtracted term is positive.
  have hlogneg : Real.log delta < 0 := Real.log_neg hd (by linarith)
  have hlogpos : 0 < |Real.log delta| := abs_pos.2 (ne_of_lt hlogneg)
  have hterm_pos : 0 < C0 * delta * Real.sqrt |Real.log delta| := by
    have := Real.sqrt_pos.2 hlogpos
    positivity
  -- The subtracted term is below `1/2`.
  have hsd : Real.sqrt delta < 1 / (2 * C0) := by
    have h4 : (0 : ℝ) < 4 * C0 ^ 2 := by positivity
    have hlt : Real.sqrt delta < Real.sqrt (1 / (4 * C0 ^ 2)) :=
      Real.sqrt_lt_sqrt hd.le hsmall
    have hval : Real.sqrt (1 / (4 * C0 ^ 2)) = 1 / (2 * C0) := by
      rw [one_div, Real.sqrt_inv, show (4 : ℝ) * C0 ^ 2 = (2 * C0) ^ 2 by ring,
        Real.sqrt_sq (by positivity), one_div]
    rwa [hval] at hlt
  have hterm_lt : C0 * delta * Real.sqrt |Real.log delta| < 1 / 2 := by
    have hchain : delta * Real.sqrt |Real.log delta| ≤ Real.sqrt delta :=
      mul_sqrt_abs_log_le_sqrt hd hd1
    have h1 : C0 * (delta * Real.sqrt |Real.log delta|) ≤ C0 * Real.sqrt delta :=
      mul_le_mul_of_nonneg_left hchain hC0.le
    have h2 : C0 * Real.sqrt delta < C0 * (1 / (2 * C0)) :=
      mul_lt_mul_of_pos_left hsd hC0
    have h3 : C0 * (1 / (2 * C0)) = 1 / 2 := by field_simp
    rw [mul_assoc]
    linarith [h1, h2, h3.le, h3.ge]
  constructor
  · rw [gammaReg, hsqrt]; linarith
  · rw [gammaReg, hsqrt]; linarith

/-- The model's own bounds feed the estimate. -/
theorem gammaReg_mem_Ioo_of_model {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {C0 : ℝ} (hC0 : 0 < C0) (hsmall : M.delta < 1 / (4 * C0 ^ 2)) :
    gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 :=
  gammaReg_mem_Ioo hC0 M.shellPrefix.delta_pos M.shellPrefix.delta_le_half hsmall

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
