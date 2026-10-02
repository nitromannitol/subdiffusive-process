import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped ENNReal
noncomputable section

namespace SubdiffusiveProcess

theorem orlicz_exp_linear_integrable_integral_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (A «λ» : ℝ)
    (hXm : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω)
    (hA : 0 < A)
    («hλ» : 0 ≤ «λ»)
    (hOrlicz :
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / A) ^ (2 : ℕ))) ∂μ) ≤ 2) :
    Integrable (fun ω => Real.exp («λ» * X ω)) μ ∧
      ∫ ω, Real.exp («λ» * X ω) ∂μ ≤
        2 * Real.exp (A ^ (2 : ℕ) * «λ» ^ (2 : ℕ) / 4) := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hsq_meas : Measurable (fun ω => Real.exp ((X ω / A) ^ (2 : ℕ))) := by
    exact ((hXm.div_const A).pow_const (2 : ℕ)).exp
  have hsq_nonneg : 0 ≤ᵐ[μ] (fun ω => Real.exp ((X ω / A) ^ (2 : ℕ))) :=
    Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)
  have hsq_finite : HasFiniteIntegral (fun ω => Real.exp ((X ω / A) ^ (2 : ℕ))) μ := by
    rw [hasFiniteIntegral_iff_ofReal hsq_nonneg]
    exact lt_of_le_of_lt hOrlicz (by norm_num)
  have hsq_int : Integrable (fun ω => Real.exp ((X ω / A) ^ (2 : ℕ))) μ :=
    ⟨hsq_meas.aestronglyMeasurable, hsq_finite⟩
  have hdom_meas : Measurable (fun ω => Real.exp («λ» * X ω)) := by
    exact (measurable_const.mul hXm).exp
  have hpoint : ∀ ω,
      Real.exp («λ» * X ω) ≤
        Real.exp (A ^ (2 : ℕ) * «λ» ^ (2 : ℕ) / 4) *
          Real.exp ((X ω / A) ^ (2 : ℕ)) := by
    intro ω
    have hyoung : «λ» * X ω ≤
        (X ω / A) ^ (2 : ℕ) + A ^ (2 : ℕ) * «λ» ^ (2 : ℕ) / 4 := by
      have hsign : 0 ≤ X ω ∧ 0 ≤ «λ» := ⟨hX0 ω, «hλ»⟩
      rcases hsign with ⟨hXω, hlambda⟩
      have hs : 0 ≤ (X ω / A - A * «λ» / 2) ^ (2 : ℕ) :=
        sq_nonneg (X ω / A - A * «λ» / 2)
      field_simp [hA0] at hs ⊢
      nlinarith [hXω, hlambda]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hdom_int : Integrable
      (fun ω => Real.exp (A ^ (2 : ℕ) * «λ» ^ (2 : ℕ) / 4) *
        Real.exp ((X ω / A) ^ (2 : ℕ))) μ := by
    exact hsq_int.const_mul _
  have hexp_int : Integrable (fun ω => Real.exp («λ» * X ω)) μ := by
    refine hdom_int.mono' hdom_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hpoint ω)
  have hsq_integral_le :
      (∫ ω, Real.exp ((X ω / A) ^ (2 : ℕ)) ∂μ) ≤ 2 := by
    have h_ofReal :
        ENNReal.ofReal (∫ ω, Real.exp ((X ω / A) ^ (2 : ℕ)) ∂μ) ≤
          (2 : ℝ≥0∞) := by
      rw [ofReal_integral_eq_lintegral_ofReal hsq_int hsq_nonneg]
      exact hOrlicz
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp
      (by simpa using h_ofReal)
  have h_integral_mono :
      (∫ ω, Real.exp («λ» * X ω) ∂μ) ≤
        ∫ ω, Real.exp (A ^ (2 : ℕ) * «λ» ^ (2 : ℕ) / 4) *
          Real.exp ((X ω / A) ^ (2 : ℕ)) ∂μ :=
    integral_mono hexp_int hdom_int (fun ω => hpoint ω)
  refine ⟨hexp_int, ?_⟩
  calc
    (∫ ω, Real.exp («λ» * X ω) ∂μ) ≤
        ∫ ω, Real.exp (A ^ (2 : ℕ) * «λ» ^ (2 : ℕ) / 4) *
          Real.exp ((X ω / A) ^ (2 : ℕ)) ∂μ := h_integral_mono
    _ = Real.exp (A ^ (2 : ℕ) * «λ» ^ (2 : ℕ) / 4) *
          (∫ ω, Real.exp ((X ω / A) ^ (2 : ℕ)) ∂μ) := by
      rw [integral_const_mul]
    _ ≤ Real.exp (A ^ (2 : ℕ) * «λ» ^ (2 : ℕ) / 4) * 2 :=
      mul_le_mul_of_nonneg_left hsq_integral_le (Real.exp_pos _).le
    _ = 2 * Real.exp (A ^ (2 : ℕ) * «λ» ^ (2 : ℕ) / 4) := by ring

end SubdiffusiveProcess
