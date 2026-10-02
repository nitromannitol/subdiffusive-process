import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.RandomFactorMeasurability
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Parameters for the cutoff Dirichlet balance

The manuscript first chooses `0 < s₁ < s < s₂ < 1` with
`s₂ / (s₁ + s₂) > ϑ`, and then takes the ceiling of the scale at
which `3^(s₁ k) δ` and `3^(-s₂ k)` balance.  This file makes one
dimension-free choice and records both ceiling inequalities and the two
balanced powers.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- A concrete lower response order. -/
def dirichletS1 (vartheta : ℝ) : ℝ := (1 - vartheta) / 8

/-- The negative-norm order used in the coarse-graining estimate. -/
def dirichletS (vartheta : ℝ) : ℝ := (1 - vartheta) / 4

/-- A fixed upper datum order. -/
def dirichletS2 (_vartheta : ℝ) : ℝ := 1 / 2

/-- The exponent produced by balancing the two geometric terms. -/
def dirichletBalanceExponent (vartheta : ℝ) : ℝ :=
  dirichletS2 vartheta / (dirichletS1 vartheta + dirichletS2 vartheta)

/-- The unrounded optimizing scale. -/
def dirichletBalanceArgument (vartheta delta : ℝ) : ℝ :=
  Real.logb 3 delta⁻¹ / (dirichletS1 vartheta + dirichletS2 vartheta)

/-- The integer optimizing scale from `e.Dirichlet.parameter.balance`. -/
def dirichletBalanceScale (vartheta delta : ℝ) : ℕ :=
  ⌈dirichletBalanceArgument vartheta delta⌉₊

theorem dirichlet_parameter_orders {vartheta : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1) :
    0 < dirichletS1 vartheta ∧
      dirichletS1 vartheta < dirichletS vartheta ∧
      dirichletS vartheta < dirichletS2 vartheta ∧
      dirichletS2 vartheta < 1 := by
  unfold dirichletS1 dirichletS dirichletS2
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The balanced exponent strictly improves the requested exponent. -/
theorem vartheta_lt_dirichletBalanceExponent {vartheta : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1) :
    vartheta < dirichletBalanceExponent vartheta := by
  unfold dirichletBalanceExponent dirichletS1 dirichletS2
  have hden : 0 < (1 - vartheta) / 8 + 1 / 2 := by linarith
  rw [lt_div_iff₀ hden]
  nlinarith

theorem dirichletBalanceArgument_nonneg {vartheta delta : ℝ}
    (hvarthetaOne : vartheta < 1) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    0 ≤ dirichletBalanceArgument vartheta delta := by
  have hinv : 1 ≤ delta⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hdelta]
    simpa using hdeltaOne
  have hlog : 0 ≤ Real.logb 3 delta⁻¹ :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 3) hinv
  have hden : 0 < dirichletS1 vartheta + dirichletS2 vartheta := by
    unfold dirichletS1 dirichletS2
    linarith
  exact div_nonneg hlog hden.le

theorem dirichletBalanceArgument_le_scale {vartheta delta : ℝ} :
    dirichletBalanceArgument vartheta delta ≤
      (dirichletBalanceScale vartheta delta : ℝ) := by
  exact Nat.le_ceil _

theorem dirichletBalanceScale_lt_argument_add_one {vartheta delta : ℝ}
    (harg : 0 ≤ dirichletBalanceArgument vartheta delta) :
    (dirichletBalanceScale vartheta delta : ℝ) <
      dirichletBalanceArgument vartheta delta + 1 := by
  exact Nat.ceil_lt_add_one harg

private theorem three_rpow_balance_decay_identity
    {s1 s2 delta : ℝ} (hsum : 0 < s1 + s2) (hdelta : 0 < delta) :
    Real.rpow 3
        (-s2 * (Real.logb 3 delta⁻¹ / (s1 + s2))) =
      Real.rpow delta (s2 / (s1 + s2)) := by
  change (3 : ℝ) ^ (-s2 * (Real.logb 3 delta⁻¹ / (s1 + s2))) =
    delta ^ (s2 / (s1 + s2))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos hdelta, Real.logb]
  congr 1
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hsumNe : s1 + s2 ≠ 0 := ne_of_gt hsum
  have hlogInv : Real.log delta⁻¹ = -Real.log delta := by
    rw [Real.log_inv]
  rw [hlogInv]
  field_simp

private theorem three_rpow_balance_growth_identity
    {s1 s2 delta : ℝ} (hsum : 0 < s1 + s2) (hdelta : 0 < delta) :
    Real.rpow 3
          (s1 * (Real.logb 3 delta⁻¹ / (s1 + s2))) * delta =
      Real.rpow delta (s2 / (s1 + s2)) := by
  change (3 : ℝ) ^ (s1 * (Real.logb 3 delta⁻¹ / (s1 + s2))) * delta =
    delta ^ (s2 / (s1 + s2))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos hdelta]
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hsumNe : s1 + s2 ≠ 0 := ne_of_gt hsum
  have hlogInv : Real.log delta⁻¹ = -Real.log delta := by
    rw [Real.log_inv]
  calc
    Real.exp (Real.log 3 *
          (s1 * (Real.logb 3 delta⁻¹ / (s1 + s2)))) * delta =
        Real.exp (Real.log 3 *
          (s1 * (Real.logb 3 delta⁻¹ / (s1 + s2)))) *
            Real.exp (Real.log delta) := by rw [Real.exp_log hdelta]
    _ = Real.exp (Real.log 3 *
          (s1 * (Real.logb 3 delta⁻¹ / (s1 + s2))) + Real.log delta) := by
      rw [Real.exp_add]
    _ = Real.exp (Real.log delta * (s2 / (s1 + s2))) := by
      congr 1
      rw [Real.logb, hlogInv]
      field_simp
      ring

/-- The decaying geometric term is below the exact balanced power. -/
theorem dirichletBalance_decay_le {vartheta delta : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1)
    (hdelta : 0 < delta) (_hdeltaOne : delta ≤ 1) :
    Real.rpow 3
        (-dirichletS2 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) ≤
      Real.rpow delta (dirichletBalanceExponent vartheta) := by
  obtain ⟨hs1, _hs1s, _hss2, _hs2one⟩ :=
    dirichlet_parameter_orders hvartheta hvarthetaOne
  have hs2 : 0 < dirichletS2 vartheta := by unfold dirichletS2; norm_num
  have hsum : 0 < dirichletS1 vartheta + dirichletS2 vartheta := by linarith
  have hceil := dirichletBalanceArgument_le_scale
    (vartheta := vartheta) (delta := delta)
  have hexp : -dirichletS2 vartheta *
        (dirichletBalanceScale vartheta delta : ℝ) ≤
      -dirichletS2 vartheta * dirichletBalanceArgument vartheta delta := by
    exact mul_le_mul_of_nonpos_left hceil (neg_nonpos.mpr hs2.le)
  calc
    Real.rpow 3
        (-dirichletS2 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) ≤
        Real.rpow 3
          (-dirichletS2 vartheta * dirichletBalanceArgument vartheta delta) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = Real.rpow delta (dirichletBalanceExponent vartheta) := by
      exact three_rpow_balance_decay_identity hsum hdelta

/-- The growing response term pays only the one-step ceiling factor. -/
theorem dirichletBalance_growth_le {vartheta delta : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    Real.rpow 3
          (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) * delta ≤
      Real.rpow 3 (dirichletS1 vartheta) *
        Real.rpow delta (dirichletBalanceExponent vartheta) := by
  obtain ⟨hs1, _hs1s, _hss2, _hs2one⟩ :=
    dirichlet_parameter_orders hvartheta hvarthetaOne
  have hs2 : 0 < dirichletS2 vartheta := by unfold dirichletS2; norm_num
  have hsum : 0 < dirichletS1 vartheta + dirichletS2 vartheta := by linarith
  have harg := dirichletBalanceArgument_nonneg hvarthetaOne hdelta hdeltaOne
  have hceil := (dirichletBalanceScale_lt_argument_add_one harg).le
  have hexp : dirichletS1 vartheta *
        (dirichletBalanceScale vartheta delta : ℝ) ≤
      dirichletS1 vartheta * (dirichletBalanceArgument vartheta delta + 1) :=
    mul_le_mul_of_nonneg_left hceil hs1.le
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  calc
    Real.rpow 3
          (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) * delta ≤
        Real.rpow 3
          (dirichletS1 vartheta * (dirichletBalanceArgument vartheta delta + 1)) * delta :=
      mul_le_mul_of_nonneg_right hpow hdelta.le
    _ = Real.rpow 3 (dirichletS1 vartheta) *
        (Real.rpow 3
          (dirichletS1 vartheta * dirichletBalanceArgument vartheta delta) * delta) := by
      change (3 : ℝ) ^
          (dirichletS1 vartheta * (dirichletBalanceArgument vartheta delta + 1)) * delta =
        (3 : ℝ) ^ (dirichletS1 vartheta) *
          ((3 : ℝ) ^
            (dirichletS1 vartheta * dirichletBalanceArgument vartheta delta) * delta)
      rw [show dirichletS1 vartheta *
          (dirichletBalanceArgument vartheta delta + 1) =
          dirichletS1 vartheta +
            dirichletS1 vartheta * dirichletBalanceArgument vartheta delta by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring
    _ = Real.rpow 3 (dirichletS1 vartheta) *
        Real.rpow delta (dirichletBalanceExponent vartheta) := by
      rw [show Real.rpow 3
            (dirichletS1 vartheta * dirichletBalanceArgument vartheta delta) * delta =
          Real.rpow delta (dirichletBalanceExponent vartheta) by
        simpa [dirichletBalanceArgument, dirichletBalanceExponent] using
          (three_rpow_balance_growth_identity hsum hdelta)]

/-- Both balanced powers are at most `delta^vartheta`. -/
theorem dirichletBalance_power_le_vartheta {vartheta delta : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    Real.rpow delta (dirichletBalanceExponent vartheta) ≤
      Real.rpow delta vartheta := by
  exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
    (vartheta_lt_dirichletBalanceExponent hvartheta hvarthetaOne).le

private theorem delta_neg_mul_balanceExponent_le_one {vartheta delta : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    Real.rpow delta (-vartheta) *
        Real.rpow delta (dirichletBalanceExponent vartheta) ≤ 1 := by
  have hgap : 0 ≤ dirichletBalanceExponent vartheta - vartheta :=
    sub_nonneg.mpr
      (vartheta_lt_dirichletBalanceExponent hvartheta hvarthetaOne).le
  have hpow : delta ^
      (dirichletBalanceExponent vartheta - vartheta) ≤ 1 :=
    Real.rpow_le_one hdelta.le hdeltaOne hgap
  change delta ^ (-vartheta) * delta ^ (dirichletBalanceExponent vartheta) ≤ 1
  rw [← Real.rpow_add hdelta]
  simpa only [neg_add_eq_sub] using hpow

/-- After multiplication by `delta^(-vartheta)`, the decaying coefficient is
at most one. -/
theorem dirichletBalancedDecayCoefficient_le_one {vartheta delta : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    Real.rpow delta (-vartheta) *
        Real.rpow 3
          (-dirichletS2 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) ≤ 1 := by
  have hdecay := dirichletBalance_decay_le
    hvartheta hvarthetaOne hdelta hdeltaOne
  exact (mul_le_mul_of_nonneg_left hdecay
    (Real.rpow_nonneg hdelta.le _)).trans
      (delta_neg_mul_balanceExponent_le_one
        hvartheta hvarthetaOne hdelta hdeltaOne)

/-- After multiplication by `delta^(-vartheta)`, the growing linear response
coefficient is bounded by the fixed one-step ceiling loss. -/
theorem dirichletBalancedGrowthCoefficient_le {vartheta delta : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    Real.rpow delta (-vartheta) *
        (Real.rpow 3
          (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) * delta) ≤
      Real.rpow 3 (dirichletS1 vartheta) := by
  have hgrowth := dirichletBalance_growth_le
    hvartheta hvarthetaOne hdelta hdeltaOne
  have hcombine := mul_le_mul_of_nonneg_left hgrowth
    (Real.rpow_nonneg hdelta.le (-vartheta))
  have hdeltaPower := delta_neg_mul_balanceExponent_le_one
    hvartheta hvarthetaOne hdelta hdeltaOne
  calc
    Real.rpow delta (-vartheta) *
        (Real.rpow 3
          (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) * delta) ≤
      Real.rpow delta (-vartheta) *
        (Real.rpow 3 (dirichletS1 vartheta) *
          Real.rpow delta (dirichletBalanceExponent vartheta)) := hcombine
    _ = Real.rpow 3 (dirichletS1 vartheta) *
        (Real.rpow delta (-vartheta) *
          Real.rpow delta (dirichletBalanceExponent vartheta)) := by ring
    _ ≤ Real.rpow 3 (dirichletS1 vartheta) * 1 :=
      mul_le_mul_of_nonneg_left hdeltaPower (Real.rpow_nonneg (by norm_num) _)
    _ = Real.rpow 3 (dirichletS1 vartheta) := mul_one _

/-- The coefficient of the normalized quadratic response `E₂² / delta²`
is bounded by the same fixed ceiling loss. -/
theorem dirichletBalancedQuadraticCoefficient_le {vartheta delta : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    Real.rpow delta (-vartheta) *
        Real.rpow 3
          (-dirichletS2 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) *
        Real.rpow 3
          (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) *
        delta ^ (2 : ℕ) ≤
      Real.rpow 3 (dirichletS1 vartheta) := by
  have hdecay := dirichletBalancedDecayCoefficient_le_one
    hvartheta hvarthetaOne hdelta hdeltaOne
  have hgrowthRaw := dirichletBalance_growth_le
    hvartheta hvarthetaOne hdelta hdeltaOne
  have hbetaOne : Real.rpow delta (dirichletBalanceExponent vartheta) ≤ 1 := by
    change delta ^ (dirichletBalanceExponent vartheta) ≤ 1
    apply Real.rpow_le_one hdelta.le hdeltaOne
    exact (show 0 < dirichletBalanceExponent vartheta by
      unfold dirichletBalanceExponent
      obtain ⟨hs1, _, _, _⟩ := dirichlet_parameter_orders hvartheta hvarthetaOne
      have hs2 : 0 < dirichletS2 vartheta := by unfold dirichletS2; norm_num
      positivity).le
  have hgrowth : Real.rpow 3
        (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) * delta ≤
      Real.rpow 3 (dirichletS1 vartheta) :=
    hgrowthRaw.trans (mul_le_of_le_one_right
      (Real.rpow_nonneg (by norm_num) _) hbetaOne)
  have hleft0 : 0 ≤ Real.rpow delta (-vartheta) *
      Real.rpow 3
        (-dirichletS2 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hdelta.le _) (Real.rpow_nonneg (by norm_num) _)
  have hgrowth0 : 0 ≤ Real.rpow 3
      (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) * delta :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hdelta.le
  have hfixed0 : 0 ≤ Real.rpow 3 (dirichletS1 vartheta) :=
    Real.rpow_nonneg (by norm_num) _
  have hproduct :
      (Real.rpow delta (-vartheta) *
          Real.rpow 3
            (-dirichletS2 vartheta * (dirichletBalanceScale vartheta delta : ℝ))) *
        (Real.rpow 3
          (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) * delta) ≤
      Real.rpow 3 (dirichletS1 vartheta) := by
    have hmul := mul_le_mul hdecay hgrowth hgrowth0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hmul
  calc
    Real.rpow delta (-vartheta) *
        Real.rpow 3
          (-dirichletS2 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) *
        Real.rpow 3
          (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) *
        delta ^ (2 : ℕ) =
      (Real.rpow delta (-vartheta) *
        Real.rpow 3
          (-dirichletS2 vartheta * (dirichletBalanceScale vartheta delta : ℝ))) *
      (Real.rpow 3
          (dirichletS1 vartheta * (dirichletBalanceScale vartheta delta : ℝ)) * delta) *
      delta := by ring
    _ ≤ Real.rpow 3 (dirichletS1 vartheta) * delta :=
      mul_le_mul_of_nonneg_right hproduct hdelta.le
    _ ≤ Real.rpow 3 (dirichletS1 vartheta) * 1 :=
      mul_le_mul_of_nonneg_left hdeltaOne hfixed0
    _ = Real.rpow 3 (dirichletS1 vartheta) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
