import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.CampanatoFull

/-!
# Hölder parameter absorption

This file isolates the only analytic arithmetic in `e.exp.lambda.bound`.
All inputs are dimension-only constants; choosing `C₁` once converts the
linear-in-window exponential into the printed quarter Hölder power.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The manuscript's `e.exp.lambda.bound`, in a reusable constant-selection
form. -/
theorem exists_holderExponentialAbsorption (A₀ P : ℝ) (hP : 0 ≤ P) :
    ∃ C₁ C : ℝ, 0 < C₁ ∧ 0 < C ∧
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
        Real.exp (A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
          C * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C₁ : ℝ := 1 + 4 * P / Real.log 3
  let C : ℝ := Real.exp (A₀ + P * C₁⁻¹)
  have hC₁ : 0 < C₁ := by
    dsimp only [C₁]
    positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C₁, C, hC₁, hC, ?_⟩
  intro alpha halpha gap hgap
  have ha0 : 0 ≤ 1 - alpha := by linarith [halpha.2]
  have ha1 : 1 - alpha ≤ 1 := by linarith [halpha.1]
  have hratio : P * C₁⁻¹ ≤ Real.log 3 / 4 := by
    rw [mul_inv_le_iff₀ hC₁]
    dsimp only [C₁]
    field_simp [hlog.ne']
    nlinarith
  have hunit : P * C₁⁻¹ * (1 - alpha) ≤ P * C₁⁻¹ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1
      (mul_nonneg hP (inv_nonneg.mpr hC₁.le))
  have hgapPart : P * C₁⁻¹ * ((1 - alpha) * gap) ≤
      Real.log 3 / 4 * ((1 - alpha) * gap) := by
    exact mul_le_mul_of_nonneg_right hratio (mul_nonneg ha0 hgap)
  have hexponent :
      A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1) ≤
        (A₀ + P * C₁⁻¹) + Real.log 3 * ((1 - alpha) * gap / 4) := by
    nlinarith
  calc
    Real.exp (A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
        Real.exp ((A₀ + P * C₁⁻¹) +
          Real.log 3 * ((1 - alpha) * gap / 4)) := Real.exp_le_exp.mpr hexponent
    _ = C * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := by
      rw [Real.exp_add]
      dsimp only [C]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]

/-- A harmless linear prefactor is absorbed by doubling the exponential
rate before applying the preceding theorem. -/
theorem exists_holderLinearExponentialAbsorption (A₀ P : ℝ) (hP : 0 ≤ P) :
    ∃ C₁ C : ℝ, 0 < C₁ ∧ 0 < C ∧
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
        (1 + C₁⁻¹ * (1 - alpha) * gap) *
            Real.exp (A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
          C * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := by
  obtain ⟨C₁, C, hC₁, hC, hbound⟩ :=
    exists_holderExponentialAbsorption A₀ (P + 1) (by linarith)
  refine ⟨C₁, C, hC₁, hC, ?_⟩
  intro alpha halpha gap hgap
  have ha0 : 0 ≤ 1 - alpha := by linarith [halpha.2]
  let x := C₁⁻¹ * (1 - alpha) * gap
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hlin : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hexp0 : 0 ≤ Real.exp (A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) :=
    (Real.exp_pos _).le
  calc
    (1 + C₁⁻¹ * (1 - alpha) * gap) *
        Real.exp (A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) =
      (1 + x) * Real.exp (A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) := by rfl
    _ ≤ Real.exp x * Real.exp
        (A₀ + P * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) :=
      mul_le_mul_of_nonneg_right hlin hexp0
    _ = Real.exp (A₀ + (P + 1) * (C₁⁻¹ * (1 - alpha)) * (gap + 1) -
        C₁⁻¹ * (1 - alpha)) := by
      rw [← Real.exp_add]
      dsimp only [x]
      congr 1
      ring
    _ ≤ Real.exp (A₀ + (P + 1) * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) := by
      apply Real.exp_le_exp.mpr
      exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hC₁.le) ha0)
    _ ≤ C * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := hbound alpha halpha gap hgap

/-- Dimension-only selection of the block length and the `epsilon`
denominator in Step 1. -/
theorem exists_holderContractionParameters (d : ℕ) (Cstep : ℝ) (hCstep : 0 < Cstep) :
    ∃ k : ℕ, ∃ C₂ : ℝ, 0 < k ∧ 1 ≤ C₂ ∧
      let theta := (3 : ℝ) ^ (-(1 / 4 : ℝ))
      theta ∈ Set.Ioo (0 : ℝ) 1 ∧ theta ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) ∧
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ C₂⁻¹ →
        Cstep * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) ≤ theta ^ k := by
  let q : ℝ := (3 : ℝ) ^ (1 / 4 : ℝ)
  have hq1 : 1 < q := by
    dsimp only [q]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hevent : ∀ᶠ N : ℕ in Filter.atTop, 2 * Cstep < q ^ N :=
    (tendsto_pow_atTop_atTop_of_one_lt hq1).eventually_gt_atTop (2 * Cstep)
  obtain ⟨N, hN⟩ := hevent.exists
  let k := max N 4
  have hkN : N ≤ k := Nat.le_max_left N 4
  have hk4 : 4 ≤ k := Nat.le_max_right N 4
  have hk : 0 < k := by omega
  have hq0 : 0 ≤ q := (zero_lt_one.trans hq1).le
  have hqpow : 2 * Cstep < q ^ k :=
    hN.trans_le (pow_le_pow_right₀ hq1.le hkN)
  let theta : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))
  have htheta0 : 0 < theta := by dsimp only [theta]; positivity
  have htheta1 : theta < 1 := by
    dsimp only [theta]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hqeq : q ^ k = (3 : ℝ) ^ ((k : ℝ) / 4) := by
    dsimp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hthetaPow : theta ^ k = (3 : ℝ) ^ (-(k : ℝ) / 4) := by
    dsimp only [theta]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hfirst : Cstep * (3 : ℝ) ^ (-(k : ℝ) / 2) ≤ theta ^ k / 2 := by
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hqpow)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(k : ℝ) / 2))
    rw [hqeq] at hmul
    have hprod : (3 : ℝ) ^ ((k : ℝ) / 4) *
        (3 : ℝ) ^ (-(k : ℝ) / 2) = theta ^ k := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hthetaPow]
      congr 1
      ring
    rw [hprod] at hmul
    linarith
  have hthetak0 : 0 < theta ^ k := pow_pos htheta0 k
  have hthetakUpper : theta ^ k < 3 / 5 := by
    have hpowle : theta ^ k ≤ theta ^ 4 :=
      pow_le_pow_of_le_one htheta0.le htheta1.le hk4
    have htheta4 : theta ^ 4 = (1 / 3 : ℝ) := by
      dsimp only [theta]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num [Real.rpow_neg_one]
    rw [htheta4] at hpowle
    linarith
  let B : ℝ := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let C₂ : ℝ := 1 + 2 * B / (theta ^ k)
  have hC₂ : 1 ≤ C₂ := by
    dsimp only [C₂]
    have : 0 ≤ 2 * B / theta ^ k := div_nonneg (mul_nonneg (by norm_num) hB) hthetak0.le
    linarith
  have hC₂pos : 0 < C₂ := zero_lt_one.trans_le hC₂
  refine ⟨k, C₂, hk, hC₂, ?_⟩
  dsimp only
  refine ⟨⟨htheta0, htheta1⟩, ⟨hthetak0, hthetakUpper⟩, ?_⟩
  intro epsilon hepsilon hepsilonC
  have hsecond : B * epsilon ≤ theta ^ k / 2 := by
    have hle := mul_le_mul_of_nonneg_left hepsilonC hB
    have hratio : B * C₂⁻¹ ≤ theta ^ k / 2 := by
      rw [mul_inv_le_iff₀ hC₂pos]
      dsimp only [C₂]
      field_simp [hthetak0.ne']
      nlinarith
    exact hle.trans hratio
  dsimp only [B] at hsecond
  nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
