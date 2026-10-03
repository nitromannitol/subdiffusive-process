module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepScales
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The manuscript's `ceil |log_3 delta|`. -/
def oneStepSourceLogThreeCeil (delta : ℝ) : ℕ :=
  ⌈|Real.log delta / Real.log 3|⌉₊

/-- The literal sixteen-logarithm buffer between the lower cutoff endpoint
and the localization cells. -/
def oneStepLocalizationDepth (delta : ℝ) : ℕ :=
  16 * oneStepSourceLogThreeCeil delta

/-- The source cell scale below a lower cutoff endpoint `n`. -/
def oneStepLocalizationScale (n : ℕ) (delta : ℝ) : ℕ :=
  n - oneStepLocalizationDepth delta

@[simp] theorem oneStepSourceLogThreeCeil_eq (delta : ℝ) :
    oneStepSourceLogThreeCeil delta =
      ⌈|Real.log delta / Real.log 3|⌉₊ := rfl

@[simp] theorem oneStepLocalizationDepth_eq (delta : ℝ) :
    oneStepLocalizationDepth delta =
      16 * ⌈|Real.log delta / Real.log 3|⌉₊ := rfl

/-- The source gate is exactly the assertion that the localization buffer
fits below the lower cutoff endpoint. -/
theorem oneStepLocalizationDepth_le {n : ℕ} {delta : ℝ}
    (hsource : 16 * ⌈|Real.log delta / Real.log 3|⌉₊ ≤ n) :
    oneStepLocalizationDepth delta ≤ n := by
  simpa [oneStepLocalizationDepth, oneStepSourceLogThreeCeil] using hsource

/-- Exact recovery of the lower cutoff endpoint from the cell scale and the
buffer, under the source gate. -/
theorem oneStepLocalizationScale_add_depth {n : ℕ} {delta : ℝ}
    (hsource : 16 * ⌈|Real.log delta / Real.log 3|⌉₊ ≤ n) :
    oneStepLocalizationScale n delta + oneStepLocalizationDepth delta = n := by
  rw [oneStepLocalizationScale, Nat.sub_add_cancel]
  exact oneStepLocalizationDepth_le hsource

/-- The high-cutoff-to-cell gap is the shell block length plus the literal
localization buffer. -/
theorem oneStep_highCutoff_sub_localizationScale {n h : ℕ} {delta : ℝ}
    (hsource : 16 * ⌈|Real.log delta / Real.log 3|⌉₊ ≤ n) :
    n + h - oneStepLocalizationScale n delta =
      h + oneStepLocalizationDepth delta := by
  have hdepth := oneStepLocalizationDepth_le hsource
  unfold oneStepLocalizationScale
  omega

private theorem logb_three_inv_eq_abs_log_div {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    Real.logb 3 delta⁻¹ = |Real.log delta / Real.log 3| := by
  have hlogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogDelta : Real.log delta ≤ 0 := Real.log_nonpos hdelta0.le hdelta1
  rw [← Real.log_div_log, Real.log_inv]
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hlogDelta hlogThree.le)]
  ring

private theorem logb_three_inv_le_sourceCeil {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    Real.logb 3 delta⁻¹ ≤ (oneStepSourceLogThreeCeil delta : ℝ) := by
  rw [logb_three_inv_eq_abs_log_div hdelta0 hdelta1]
  exact Nat.le_ceil _

/-- The exact scale gain used in Step 1:
`3^(-16 ceil |log_3 delta|) ≤ delta^16`. -/
theorem rpow_three_neg_oneStepLocalizationDepth_le_delta_pow_sixteen
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (3 : ℝ) ^ (-(oneStepLocalizationDepth delta : ℝ)) ≤
      delta ^ (16 : ℕ) := by
  have hx0 : 0 < delta⁻¹ := inv_pos.mpr hdelta0
  have hceil := logb_three_inv_le_sourceCeil hdelta0 hdelta1
  have hexponent :
      Real.logb 3 delta⁻¹ * (16 : ℝ) ≤
        (oneStepLocalizationDepth delta : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hceil (by norm_num : (0 : ℝ) ≤ 16)
    rw [oneStepLocalizationDepth, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hrepr : delta⁻¹ = (3 : ℝ) ^ Real.logb 3 delta⁻¹ :=
    (Real.rpow_logb (by norm_num) (by norm_num) hx0).symm
  have hmaster : delta⁻¹ ^ (16 : ℝ) ≤
      (3 : ℝ) ^ (oneStepLocalizationDepth delta : ℝ) := by
    calc
      delta⁻¹ ^ (16 : ℝ) =
          ((3 : ℝ) ^ Real.logb 3 delta⁻¹) ^ (16 : ℝ) := by rw [← hrepr]
      _ = (3 : ℝ) ^ (Real.logb 3 delta⁻¹ * 16) :=
        (Real.rpow_mul (by norm_num) _ _).symm
      _ ≤ (3 : ℝ) ^ (oneStepLocalizationDepth delta : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hdeltaPow : 0 < delta ^ (16 : ℕ) := pow_pos hdelta0 16
  rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) hdeltaPow]
  have hinv : delta⁻¹ ^ (16 : ℝ) = (delta ^ (16 : ℕ))⁻¹ := by
    rw [Real.inv_rpow hdelta0.le]
    norm_num
  rw [← hinv]
  exact hmaster

/-- Spending one of the sixteen localization powers gives the manuscript's
`delta^15` cell-oscillation budget. -/
theorem rpow_three_neg_oneStepLocalizationDepth_le_delta_pow_fifteen
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (3 : ℝ) ^ (-(oneStepLocalizationDepth delta : ℝ)) ≤
      delta ^ (15 : ℕ) := by
  exact (rpow_three_neg_oneStepLocalizationDepth_le_delta_pow_sixteen
    hdelta0 hdelta1).trans (by
      have hnonneg : 0 ≤ delta ^ (15 : ℕ) := pow_nonneg hdelta0.le 15
      nlinarith [show delta ^ (16 : ℕ) = delta ^ (15 : ℕ) * delta by ring])

/-- A sufficiently small positive weighted-depth exponent costs at most a
universal factor after multiplication by one power of `delta`.  This is the
source-scale form used when the finite descendant maximum has already paid
its cardinality root. -/
theorem delta_mul_rpow_three_oneStepLocalizationDepth_le_three
    {delta a : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 16) :
    delta * Real.rpow 3 (a * (oneStepLocalizationDepth delta : ℝ)) ≤ 3 := by
  let x : ℝ := |Real.log delta / Real.log 3|
  have hx0 : 0 ≤ x := abs_nonneg _
  have hx : x = Real.logb 3 delta⁻¹ := by
    exact (logb_three_inv_eq_abs_log_div hdelta0 hdelta1).symm
  have hceil : (oneStepSourceLogThreeCeil delta : ℝ) ≤ x + 1 := by
    exact (Nat.ceil_lt_add_one hx0).le
  have hdepth : (oneStepLocalizationDepth delta : ℝ) ≤ 16 * (x + 1) := by
    rw [oneStepLocalizationDepth, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hexponent : a * (oneStepLocalizationDepth delta : ℝ) ≤ x + 1 := by
    have haMul := mul_le_mul_of_nonneg_left hdepth ha0
    have hx1 : 0 ≤ x + 1 := by linarith
    have h16a : 16 * a ≤ 1 := by nlinarith
    nlinarith
  have hpow : Real.rpow 3 (a * (oneStepLocalizationDepth delta : ℝ)) ≤
      Real.rpow 3 (x + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hrepr : delta⁻¹ = Real.rpow 3 x := by
    rw [hx]
    exact (Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.mpr hdelta0)).symm
  calc
    delta * Real.rpow 3 (a * (oneStepLocalizationDepth delta : ℝ)) ≤
        delta * Real.rpow 3 (x + 1) :=
      mul_le_mul_of_nonneg_left hpow hdelta0.le
    _ = delta * (Real.rpow 3 x * Real.rpow 3 1) := by
      congr 1
      change (3 : ℝ) ^ (x + 1) = (3 : ℝ) ^ x * (3 : ℝ) ^ (1 : ℝ)
      exact Real.rpow_add (by norm_num) x 1
    _ = 3 := by
      rw [← hrepr]
      norm_num
      field_simp [hdelta0.ne']

/-- The logarithmic loss in the closed Section 4 recursion costs at most one
power of the disorder on the standing range `delta <= 1`. -/
theorem delta_sq_mul_abs_log_le_self {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    delta ^ 2 * |Real.log delta| ≤ delta := by
  have hlog : Real.log delta ≤ 0 := Real.log_nonpos hdelta0.le hdelta1
  have hbasic : delta * |Real.log delta| ≤ 1 := by
    have h := Real.abs_log_mul_self_lt delta hdelta0 hdelta1
    rw [abs_mul, abs_of_nonneg hdelta0.le, mul_comm] at h
    exact h.le
  have hdeltaNonneg : 0 ≤ delta := hdelta0.le
  calc
    delta ^ 2 * |Real.log delta| = delta * (delta * |Real.log delta|) := by ring
    _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hbasic hdeltaNonneg
    _ = delta := mul_one _

/-! ## Literal fourth-moment exponents -/

/-- The fourth power of the source's `delta^15` oscillation scale is the
literal `delta^60` moment budget used after the origin-cell specialization. -/
theorem oneStep_delta_fifteen_four (C delta : ℝ) :
    (C * delta ^ (15 : ℕ)) ^ (4 : ℕ) =
      C ^ (4 : ℕ) * delta ^ (60 : ℕ) := by
  ring

/-- The fourth power of the source's `delta^17` Hessian scale is the literal
`delta^68` moment budget. -/
theorem oneStep_delta_seventeen_four (C delta : ℝ) :
    (C * delta ^ (17 : ℕ)) ^ (4 : ℕ) =
      C ^ (4 : ℕ) * delta ^ (68 : ℕ) := by
  ring



theorem oneStep_origin_cell_moment_powers
    {Omega : Type*} [MeasurableSpace Omega] (mu : MeasureTheory.Measure Omega)
    (A B : Omega → ℝ) (C delta : ℝ)
    (hA : ∫ omega, A omega ^ (4 : ℕ) ∂mu ≤
      (C * delta ^ (15 : ℕ)) ^ (4 : ℕ))
    (hB : ∫ omega, B omega ^ (4 : ℕ) ∂mu ≤
      (C * delta ^ (17 : ℕ)) ^ (4 : ℕ)) :
    (∫ omega, A omega ^ (4 : ℕ) ∂mu ≤
        C ^ (4 : ℕ) * delta ^ (60 : ℕ)) ∧
      (∫ omega, B omega ^ (4 : ℕ) ∂mu ≤
        C ^ (4 : ℕ) * delta ^ (68 : ℕ)) := by
  simpa only [oneStep_delta_fifteen_four, oneStep_delta_seventeen_four]
    using And.intro hA hB

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
