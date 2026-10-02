/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.Section9.SmallDisorderExponent
import SubdiffusiveProcess.Section9.LowerTailBootstrap

/-! # Simultaneous small-disorder budgets for the lower-tail bootstrap -/

namespace SubdiffusiveProcess.Section9

open Filter

/-- For a fixed source exponent constant, one disorder threshold supplies all
three numerical budgets used by the recursive and Gaussian half estimates. -/
theorem exists_smallDisorderBootstrap_threshold
    {cstar a U cGaussian : ℝ} (hcstar : 0 < cstar) (ha : 0 < a)
    (hU : 0 < U) (hcGaussian : 0 < cGaussian) (C : ℝ) :
    ∃ δzero : ℝ, 0 < δzero ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δzero →
      let p := smallDisorderExponent cstar δ
      2 ≤ p ∧
      2 * Real.log 2 ≤ a * p * U ∧
      a * p ≤ cGaussian * U / (8 * δ ^ 2) ∧
      Real.log (2 * max C 1) ≤ cGaussian * U ^ 2 / (8 * δ ^ 2) := by
  have htarget : 0 < (2 * Real.log 2) / (a * U) := by positivity
  have hpLarge := eventually_smallDisorderExponent_exp_neg_ge cstar
    (max 2 ((2 * Real.log 2) / (a * U))) hcstar
  rw [eventually_atTop] at hpLarge
  obtain ⟨T₁, hT₁⟩ := hpLarge
  let R₂ : ℝ := 8 * a * cstar / (cGaussian * U)
  let K : ℝ := Real.log (2 * max C 1)
  have hK : 0 ≤ K := Real.log_nonneg (by
    have hm : (1 : ℝ) ≤ max C 1 := le_max_right _ _
    nlinarith)
  have hexp := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).eventually_ge_atTop
      (8 * K / (cGaussian * U ^ 2))
  rw [eventually_atTop] at hexp
  obtain ⟨T₃, hT₃⟩ := hexp
  let T : ℝ := max 1 (max T₁ (max R₂ T₃))
  let δzero : ℝ := Real.exp (-T)
  refine ⟨δzero, Real.exp_pos _, ?_⟩
  intro δ hδ hδzero
  let t : ℝ := -Real.log δ
  have htT : T ≤ t := by
    have hlog := Real.log_le_log hδ hδzero
    dsimp [δzero] at hlog
    rw [Real.log_exp] at hlog
    dsimp [t]
    linarith
  have ht1 : 1 ≤ t := (le_max_left _ _).trans htT
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hδexp : Real.exp (-t) = δ := by
    dsimp [t]
    rw [neg_neg, Real.exp_log hδ]
  have hpbound := hT₁ t ((le_max_left T₁ (max R₂ T₃)).trans
    ((le_max_right 1 _).trans htT))
  have hp2 : 2 ≤ smallDisorderExponent cstar δ := by
    rw [← hδexp]
    exact (le_max_left _ _).trans hpbound
  have hrec : 2 * Real.log 2 ≤
      a * smallDisorderExponent cstar δ * U := by
    have hpRate : (2 * Real.log 2) / (a * U) ≤
        smallDisorderExponent cstar δ := by
      rw [← hδexp]
      exact (le_max_right _ _).trans hpbound
    have haU : 0 < a * U := mul_pos ha hU
    exact (div_le_iff₀ haU).mp hpRate |>.trans_eq (by ring)
  have htR₂ : R₂ ≤ t := (le_max_left R₂ T₃).trans
    ((le_max_right T₁ _).trans ((le_max_right 1 _).trans htT))
  have hrate : a * smallDisorderExponent cstar δ ≤
      cGaussian * U / (8 * δ ^ 2) := by
    have hid := smallDisorderExponent_exp_neg_mul_sq cstar t ht0.ne'
    rw [hδexp] at hid
    have htSq : R₂ ≤ t ^ 2 := by
      have : t ≤ t ^ 2 := by nlinarith
      exact htR₂.trans this
    dsimp [R₂] at htSq
    have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht0
    apply (le_div_iff₀ (by positivity : 0 < 8 * δ ^ 2)).2
    field_simp [ht2.ne'] at hid
    have hpos : 0 < cGaussian * U := mul_pos hcGaussian hU
    have htSq' : 8 * a * cstar ≤ t ^ 2 * (cGaussian * U) :=
      (div_le_iff₀ hpos).mp htSq
    nlinarith
  have htT₃ : T₃ ≤ t := (le_max_right R₂ T₃).trans
    ((le_max_right T₁ _).trans ((le_max_right 1 _).trans htT))
  have hexpBound := hT₃ t htT₃
  have hlog : K ≤ cGaussian * U ^ 2 / (8 * δ ^ 2) := by
    rw [← hδexp]
    dsimp [K] at hK ⊢
    rw [Real.exp_neg, inv_pow]
    have hepos : 0 < Real.exp t ^ 2 := by positivity
    simp only [Function.comp_apply, id_eq] at hexpBound
    have hexpBound' : 8 * K / (cGaussian * U ^ 2) ≤ Real.exp t ^ 2 := by
      simpa only [← Real.exp_nat_mul] using hexpBound
    dsimp [K] at hexpBound
    have hden : 0 < cGaussian * U ^ 2 := by positivity
    have hb := (div_le_iff₀ hden).mp hexpBound'
    apply (le_div_iff₀ (by positivity : 0 < 8 * (Real.exp t ^ 2)⁻¹)).2
    field_simp [hepos.ne']
    nlinarith
  exact ⟨hp2, hrec, hrate, hlog⟩

end SubdiffusiveProcess.Section9
