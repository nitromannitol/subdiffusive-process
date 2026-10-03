module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

namespace SubdiffusiveProcess.RawLp

/-- Exact old eLpNorm branch formula, with no measurability guard. -/
def eLpNorm {α ε : Type*} [MeasurableSpace α] [ENorm ε]
    (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ
  else eLpNorm' f (ENNReal.toReal p) μ

theorem eLpNorm_eq_guarded {α ε : Type*} [MeasurableSpace α]
    [ENorm ε] [TopologicalSpace ε] {f : α → ε} {p : ℝ≥0∞} {μ : Measure α}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ = MeasureTheory.eLpNorm f p μ := by
  simp only [eLpNorm, MeasureTheory.eLpNorm, ite_eq_left hf]

theorem eLpNorm_le_guarded {α ε : Type*} [MeasurableSpace α]
    [ENorm ε] [TopologicalSpace ε] (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm f p μ ≤ MeasureTheory.eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact (eLpNorm_eq_guarded hf).le
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top

theorem old_memLp_iff_guarded {α ε : Type*} [MeasurableSpace α]
    [ENorm ε] [TopologicalSpace ε] (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    (AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞) ↔ MemLp f p μ := by
  constructor
  · rintro ⟨hf, hfinite⟩
    rw [eLpNorm_eq_guarded hf] at hfinite
    exact hfinite
  · intro hf
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_guarded hf.aestronglyMeasurable]
    exact hf.eLpNorm_lt_top

theorem eLpNorm_zero_exponent {α ε : Type*} [MeasurableSpace α] [ENorm ε]
    (f : α → ε) (μ : Measure α) : eLpNorm f 0 μ = 0 := by
  simp [eLpNorm]

theorem eLpNorm_top_exponent {α ε : Type*} [MeasurableSpace α] [ENorm ε]
    (f : α → ε) (μ : Measure α) : eLpNorm f ∞ μ = eLpNormEssSup f μ := by
  simp [eLpNorm]

theorem eLpNorm_eq_raw_integral {α ε : Type*} [MeasurableSpace α] [ENorm ε]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (f : α → ε) (μ : Measure α) :
    eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  simp only [eLpNorm, ite_eq_right hp0, ite_eq_right hpt,
    eLpNorm'_eq_lintegral_enorm]

theorem eLpNorm_mono_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {f g : α → ℝ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm f p μ ≤ eLpNorm g p μ := by
  by_cases hp0 : p = 0
  · simp [eLpNorm, hp0]
  by_cases hpt : p = ∞
  · have hEN : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ :=
      h.mono fun _ hx => enorm_le_iff_norm_le.mpr hx
    simpa [eLpNorm, hpt]
      using eLpNormEssSup_mono_enorm_ae hEN
  · simpa only [eLpNorm, ite_eq_right hp0, ite_eq_right hpt]
      using eLpNorm'_mono_ae ENNReal.toReal_nonneg h

end SubdiffusiveProcess.RawLp
