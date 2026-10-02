import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-!
# The Stampacchia level-set inequalities
-/

open MeasureTheory Set Filter

namespace SubdiffusiveProcess.FractionalSup

variable {X : Type*} [MeasurableSpace X]

/-- Hölder on a level set: a nonnegative `L^p` function vanishing off `A` has
`∫ f ≤ ‖f‖_p μ(A)^{1-1/p}`. -/
theorem integral_le_of_supp (μ : Measure X) [IsFiniteMeasure μ] {p : ℝ} (hp : 1 < p)
    {f : X → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hfp : MemLp f (ENNReal.ofReal p) μ)
    {A : Set X} (hA : MeasurableSet A) (hsupp : ∀ᵐ x ∂μ, x ∉ A → f x = 0) :
    ∫ x, f x ∂μ ≤ (∫ x, f x ^ p ∂μ) ^ (1 / p) * μ.real A ^ (1 - 1 / p) := by
  set q : ℝ := p / (p - 1) with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq1 : 1 / q = 1 - 1 / p := by
    rw [hq]; field_simp
  have hg_nonneg : 0 ≤ᵐ[μ] A.indicator (fun _ => (1 : ℝ)) :=
    Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hgq : MemLp (A.indicator (fun _ => (1 : ℝ))) (ENNReal.ofReal q) μ :=
    memLp_indicator_const _ hA _ (Or.inr (measure_ne_top μ A))
  have hfg : ∫ x, f x ∂μ = ∫ x, f x * A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with x hx
    by_cases hxA : x ∈ A
    · simp [hxA]
    · simp [hxA, hx hxA]
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg_nonneg hfp hgq
  have hgpow : ∫ x, A.indicator (fun _ => (1 : ℝ)) x ^ q ∂μ = μ.real A := by
    have : (fun x => A.indicator (fun _ => (1 : ℝ)) x ^ q) = A.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ A
      · simp [hx]
      · simp [hx, Real.zero_rpow (by linarith [hpq.symm.pos] : q ≠ 0)]
    rw [this, integral_indicator hA]
    simp
  rw [hfg]
  rw [hgpow, hq1] at hH
  exact hH

/-- The one-step level-set inequality from the energy/embedding bound. -/
theorem levelset_step (μ : Measure X) [IsFiniteMeasure μ] {p : ℝ} (hp : 1 < p)
    {f : X → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hfp : MemLp f (ENNReal.ofReal p) μ)
    {A : Set X} (hA : MeasurableSet A) (hsupp : ∀ᵐ x ∂μ, x ∉ A → f x = 0)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (henergy : (∫ x, f x ^ p ∂μ) ^ (2 / p) ≤ Λ * ∫ x, f x ∂μ) :
    ∫ x, f x ^ p ∂μ ≤ Λ ^ p * μ.real A ^ (p - 1) := by
  set I := ∫ x, f x ^ p ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg_of_ae (hf0.mono fun x hx => Real.rpow_nonneg hx p)
  have hm0 : 0 ≤ μ.real A := measureReal_nonneg
  have hpp : 0 < p := by linarith
  have hJ := integral_le_of_supp μ hp hf0 hfp hA hsupp
  rw [← hI] at hJ
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (Real.rpow_nonneg hΛ p) (Real.rpow_nonneg hm0 _)
  · have hI1 : 0 < I ^ (1 / p) := Real.rpow_pos_of_pos hpos _
    have h2 : I ^ (2 / p) = I ^ (1 / p) * I ^ (1 / p) := by
      rw [← Real.rpow_add hpos]; congr 1; ring
    have hchain : I ^ (1 / p) * I ^ (1 / p) ≤ Λ * (I ^ (1 / p) * μ.real A ^ (1 - 1 / p)) := by
      rw [← h2]
      exact henergy.trans (mul_le_mul_of_nonneg_left hJ hΛ)
    have hdiv : I ^ (1 / p) ≤ Λ * μ.real A ^ (1 - 1 / p) := by
      have : I ^ (1 / p) * I ^ (1 / p) ≤ (Λ * μ.real A ^ (1 - 1 / p)) * I ^ (1 / p) := by
        calc _ ≤ _ := hchain
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hI1
    have hpow := Real.rpow_le_rpow hI1.le hdiv hpp.le
    rw [← Real.rpow_mul hpos.le, one_div, inv_mul_cancel₀ hpp.ne', Real.rpow_one,
      Real.mul_rpow hΛ (Real.rpow_nonneg hm0 _), ← Real.rpow_mul hm0] at hpow
    convert hpow using 3
    field_simp

/-- Chebyshev on a level set: `(h-k)^p μ(v > h) ≤ ∫ ψ_k^p` for `ψ_k = (v-k)_+`. -/
theorem markov_level (μ : Measure X) [IsFiniteMeasure μ] {p : ℝ} (hp : 0 < p)
    {v : X → ℝ} {k h : ℝ} (hkh : k ≤ h)
    (hfp : Integrable (fun x => max (v x - k) 0 ^ p) μ) :
    (h - k) ^ p * μ.real {x | h < v x} ≤ ∫ x, max (v x - k) 0 ^ p ∂μ := by
  have hnn : 0 ≤ᵐ[μ] fun x => max (v x - k) 0 ^ p :=
    Eventually.of_forall fun x => Real.rpow_nonneg (le_max_right _ _) p
  have := mul_meas_ge_le_integral_of_nonneg hnn hfp ((h - k) ^ p)
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) p)) this
  apply measureReal_mono
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    apply Real.rpow_le_rpow (by linarith)
    · exact le_max_of_le_left (by linarith)
    · exact hp.le
  · exact measure_ne_top μ _

end SubdiffusiveProcess.FractionalSup
