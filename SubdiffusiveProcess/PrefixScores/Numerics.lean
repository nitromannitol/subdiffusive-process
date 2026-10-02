import Mathlib

/-! Finite-interval normalization and elementary tail bookkeeping. -/
open MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.PrefixScores

lemma delta_sq_log_le_self {delta : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) :
    delta ^ 2 * |Real.log delta| ≤ delta := by
  have h := (Real.abs_log_mul_self_lt delta hd hd1).le
  rw [abs_mul, abs_of_pos hd] at h
  nlinarith [mul_le_mul_of_nonneg_left h hd.le]

lemma sum_window {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.range k, f (n + i) = ∑ m ∈ Finset.Icc n (n + (k - 1)), f m := by
  have hset : Finset.Icc n (n + (k - 1)) = Finset.Ico n (n + k) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hset, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

lemma exp_moment_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (E : Set Ω) (L : ℝ)
    (hbound : ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω)) ∂μ ≤ 2)
    (hE : ∀ ω ∈ E, L ≤ Y ω) :
    μ E ≤ ENNReal.ofReal (2 * Real.exp (-L)) := by
  have hmark := meas_ge_le_lintegral_div (μ := μ)
    (hY.exp.ennreal_ofReal.aemeasurable)
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos L))) ENNReal.ofReal_ne_top
  have hsub : E ⊆ {ω | ENNReal.ofReal (Real.exp L) ≤ ENNReal.ofReal (Real.exp (Y ω))} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hE ω hω))
  calc
    μ E ≤ μ {ω | ENNReal.ofReal (Real.exp L) ≤ ENNReal.ofReal (Real.exp (Y ω))} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω)) ∂μ) / ENNReal.ofReal (Real.exp L) := hmark
    _ ≤ 2 / ENNReal.ofReal (Real.exp L) := ENNReal.div_le_div_right hbound _
    _ = ENNReal.ofReal (2 * Real.exp (-L)) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_div_of_pos (Real.exp_pos L), Real.exp_neg]
      congr 1

lemma squareAverage_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (a b t B W : ℝ)
    (hb : 0 < b) (hW : 0 < W) (ht : 0 < t)
    (ha : a ≤ t / 2) (hbudget : b ^ 2 * (B * W) ≤ (t / 2) ^ 2)
    (hbound : ∫⁻ ω, ENNReal.ofReal (Real.exp ((b⁻¹ * max (X ω / W - a) 0) ^ (2 : ℕ))) ∂μ ≤ 2) :
    μ {ω | t * W < X ω} ≤ ENNReal.ofReal (2 * Real.exp (-(B * W))) := by
  apply exp_moment_tail μ (fun ω => (b⁻¹ * max (X ω / W - a) 0) ^ (2 : ℕ))
    (by fun_prop) _ (B * W) hbound
  intro ω hω
  have hx : t < X ω / W := (lt_div_iff₀ hW).mpr (by simpa only [mul_comm] using hω)
  have hm : t / 2 ≤ max (X ω / W - a) 0 := by
    exact (by linarith : t / 2 ≤ X ω / W - a).trans (le_max_left _ _)
  have hsq : (t / 2) ^ 2 ≤ (max (X ω / W - a) 0) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hm 2
  have hm' := hbudget.trans hsq
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have h := (le_div_iff₀ hb2).mpr (by simpa only [mul_comm] using hm')
  calc
    B * W ≤ (max (X ω / W - a) 0) ^ 2 / b ^ 2 := h
    _ = (b⁻¹ * max (X ω / W - a) 0) ^ 2 := by ring

lemma rate_of_budget {C V Q B : ℝ} (hCV : 0 < C * V)
    (h : C * V * B ≤ Q) : B ≤ Q / (C * V) := by
  apply (le_div_iff₀ hCV).mpr
  simpa only [mul_comm] using h

lemma density_budget {t e theta C V : ℝ} (p : ℕ) (ht : 0 < t) (he : 0 < e)
    (h : C * V ≤ t ^ p * e ^ 2 * theta) :
    C * t ^ (-(p : ℤ)) * e⁻¹ ^ 2 * V ≤ theta := by
  have hden : 0 < t ^ p * e ^ 2 := by positivity
  have h' := (div_le_iff₀ hden).mpr (by simpa only [mul_comm, mul_left_comm, mul_assoc] using h)
  convert h' using 1
  rw [zpow_neg, zpow_natCast]
  field_simp

end SubdiffusiveProcess.PrefixScores
