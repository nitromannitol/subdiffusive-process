module

public import SubdiffusiveProcess.Section10.PhysicalExitChainingEpochs

@[expose] public section

/-! Numerical choices for the successive-exit argument. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalExitChaining

theorem exp_neg_two_le_quarter : Real.exp (-2) ≤ 1 / 4 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h4

theorem exitWeight_integral_le_half {d : ℕ}
    (k : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel k]
    (x : Vec d) (U : Set (Vec d)) (hU : IsOpen U) (h1 : ℝ) (hh1 : 0 < h1)
    (hsmall : k x {p | ContinuousPath.exitTime U p ≤ ENNReal.ofReal h1} ≤
      ENNReal.ofReal (1 / 8)) :
    (∫⁻ p, exitWeight (h1 / 2) (ContinuousPath.exitTime U p) ∂k x) ≤
      ENNReal.ofReal (1 / 2) := by
  have hh : 0 < h1 / 2 := by positivity
  have hm := ContinuousPath.measurable_exitTime U hU
  have hexp : Real.exp (-h1 / (h1 / 2)) ≤ 1 / 4 := by
    have heq : -h1 / (h1 / 2) = (-2 : ℝ) := by field_simp
    rw [heq]
    exact exp_neg_two_le_quarter
  calc
    _ ≤ ∫⁻ p, ({s : ENNReal | s ≤ ENNReal.ofReal h1}.indicator
        (1 : ENNReal → ENNReal) (ContinuousPath.exitTime U p) +
          ENNReal.ofReal (Real.exp (-h1 / (h1 / 2)))) ∂k x :=
      lintegral_mono fun p => exitWeight_le_split hh hh1.le _
    _ = k x {p | ContinuousPath.exitTime U p ≤ ENNReal.ofReal h1} +
        ENNReal.ofReal (Real.exp (-h1 / (h1 / 2))) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      congr 1
      have heq : (fun p : ContinuousPath (Vec d) =>
          {s : ENNReal | s ≤ ENNReal.ofReal h1}.indicator
            (1 : ENNReal → ENNReal) (ContinuousPath.exitTime U p)) =
          {p : ContinuousPath (Vec d) | ContinuousPath.exitTime U p ≤ ENNReal.ofReal h1}.indicator
            (1 : ContinuousPath (Vec d) → ENNReal) := by
        funext p
        simp only [Set.indicator, mem_ofPred_eq, Pi.one_apply]
      rw [heq, lintegral_indicator_one (measurableSet_le hm measurable_const)]
    _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 4) :=
      add_le_add hsmall (ENNReal.ofReal_le_ofReal hexp)
    _ ≤ ENNReal.ofReal (1 / 2) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem geometric_error_le {epsilon E : ℝ} (hepsilon : 0 < epsilon)
    (hE : 0 ≤ E) (n : ℕ) (hn : 16 * E / epsilon < (2 : ℝ) ^ n) :
    ENNReal.ofReal E * ENNReal.ofReal (1 / 2 : ℝ) ^ n ≤
      ENNReal.ofReal (epsilon / 16) := by
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hhalf : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by
    simp [one_div, inv_pow]
  have hr : E * (1 / 2 : ℝ) ^ n ≤ epsilon / 16 := by
    rw [hhalf]
    have hn' := (div_lt_iff₀ hepsilon).mp hn
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
    have hm := mul_le_mul_of_nonneg_right hn'.le (inv_pos.mpr hpow).le
    field_simp [ne_of_gt hpow] at hm ⊢
    nlinarith
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul hE]
  exact ENNReal.ofReal_le_ofReal hr

theorem short_gap_error_le {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (n : ℕ) :
    (n : ENNReal) * ENNReal.ofReal (epsilon / (16 * ((n : ℝ) + 1))) ≤
      ENNReal.ofReal (epsilon / 16) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hr : (n : ℝ) * (epsilon / (16 * ((n : ℝ) + 1))) ≤ epsilon / 16 := by
    have hratio : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hn).2
      linarith
    have heq : (n : ℝ) * (epsilon / (16 * ((n : ℝ) + 1))) =
        (epsilon / 16) * ((n : ℝ) / ((n : ℝ) + 1)) := by field_simp
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hratio (by positivity)).trans_eq (mul_one _)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  exact ENNReal.ofReal_le_ofReal hr

end SubdiffusiveProcess.Section10.PhysicalExitChaining
