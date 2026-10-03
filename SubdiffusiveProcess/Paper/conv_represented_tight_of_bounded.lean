module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology

noncomputable section
namespace Paper

/-- Uniform `L¹` bounds give boundedness in probability. -/
theorem aux_conv_represented_tight_of_bounded_L1_bounded
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ n, ∫⁻ ω, ‖Y n ω‖ₑ ∂P ≤ ENNReal.ofReal B) :
    ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n, P {ω | Mb < |Y n ω|} ≤ ENNReal.ofReal rho := by
  intro rho hrho
  set R : ℝ := B / rho + 1 with hR
  have hRpos : 0 < R := by positivity
  refine ⟨R, fun n => ?_⟩
  have hsub : {ω | R < |Y n ω|} ⊆ {ω | ENNReal.ofReal R ≤ ‖Y n ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal hω.le
  have hmarkov : ENNReal.ofReal R * P {ω | ENNReal.ofReal R ≤ ‖Y n ω‖ₑ} ≤
      ∫⁻ ω, ‖Y n ω‖ₑ ∂P :=
    mul_meas_ge_le_lintegral₀ (hY n).enorm.aemeasurable _
  have hBR : B ≤ rho * R := by
    have : B / rho < R := by rw [hR]; linarith
    rw [div_lt_iff₀ hrho] at this
    linarith
  have hle : ENNReal.ofReal R * P {ω | ENNReal.ofReal R ≤ ‖Y n ω‖ₑ} ≤
      ENNReal.ofReal R * ENNReal.ofReal rho := by
    calc ENNReal.ofReal R * P {ω | ENNReal.ofReal R ≤ ‖Y n ω‖ₑ}
        ≤ ∫⁻ ω, ‖Y n ω‖ₑ ∂P := hmarkov
      _ ≤ ENNReal.ofReal B := hB n
      _ ≤ ENNReal.ofReal (R * rho) := ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ENNReal.ofReal R * ENNReal.ofReal rho := ENNReal.ofReal_mul hRpos.le
  have hcancel := (ENNReal.mul_le_mul_iff_right (a := ENNReal.ofReal R)
    (by simpa using hRpos) ENNReal.ofReal_ne_top).1 hle
  exact (measure_mono hsub).trans hcancel

/-- **Real random variables that are bounded in probability have a tight family of laws.**
This is the elementary compact-set (`closedBall`) argument; it is used for the
constants and quadratic tests, and adds no model-specific content. -/
theorem conv_represented_tight_of_bounded
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hbdd : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n, P {ω | Mb < |Y n ω|} ≤ ENNReal.ofReal rho) :
    IsTightMeasureSet (Set.range fun n => Measure.map (Y n) P) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨∅, isCompact_empty, fun μ _ => le_top⟩
  have hepos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨Mb, hMb⟩ := hbdd ε.toReal hepos
  refine ⟨Metric.closedBall (0 : ℝ) Mb, isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hmeas : MeasurableSet (Metric.closedBall (0 : ℝ) Mb)ᶜ :=
    (Metric.isClosed_closedBall.measurableSet).compl
  rw [Measure.map_apply (hY n) hmeas]
  have hsub : (Y n ⁻¹' (Metric.closedBall (0 : ℝ) Mb)ᶜ) = {ω | Mb < |Y n ω|} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      not_le, Set.mem_setOf_eq, Real.norm_eq_abs]
  rw [hsub]
  exact (hMb n).trans (by rw [ENNReal.ofReal_toReal hεtop])

end Paper
