module

public import SubdiffusiveProcess.Static.LocalEstimateClauses

@[expose] public section

/-! # Scalar comparison of the literal mass-growth clause -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Static
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Multiplying the random constant transports both mass-growth directions. -/
theorem localMassEstimates_of_comparison {d : ℕ} {b0 b1 : Vec d → ℝ}
    {y0 : Vec d} {ρ0 K F : ℝ} (hF : 1 ≤ F)
    (hbLow : ∀ x ∈ Metric.ball y0 (ρ0 / 2), F⁻¹ * b0 x ≤ b1 x)
    (hbUp : ∀ x ∈ Metric.ball y0 (ρ0 / 2), b1 x ≤ F * b0 x)
    (h : localMassEstimates b0 y0 ρ0 K) :
    localMassEstimates b1 y0 ρ0 (F * K) := by
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hFinv : 0 ≤ F⁻¹ := inv_nonneg.mpr hF0
  intro x r hr hr1 hsub
  obtain ⟨hlo, hup⟩ := h x r hr hr1 hsub
  have hball : MeasurableSet (Metric.ball x r) := Metric.isOpen_ball.measurableSet
  have hml : ENNReal.ofReal F⁻¹ *
      volume.withDensity (fun z => ENNReal.ofReal (b0 z)) (Metric.ball x r) ≤
        volume.withDensity (fun z => ENNReal.ofReal (b1 z)) (Metric.ball x r) := by
    rw [density_mass_eq_lintegral _ hball, density_mass_eq_lintegral _ hball]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hball] with z hz
    rw [← ENNReal.ofReal_mul hFinv]
    exact ENNReal.ofReal_le_ofReal (hbLow z (hsub hz))
  have hmu : volume.withDensity (fun z => ENNReal.ofReal (b1 z)) (Metric.ball x r) ≤
      ENNReal.ofReal F *
        volume.withDensity (fun z => ENNReal.ofReal (b0 z)) (Metric.ball x r) := by
    rw [density_mass_eq_lintegral _ hball, density_mass_eq_lintegral _ hball]
    exact lintegral_ofReal_le_mul volume hball hF0 (fun z hz => hbUp z (hsub hz))
  constructor
  · calc
      ENNReal.ofReal ((F * K)⁻¹ * r ^ ((d : ℝ) + 1 / 2)) =
          ENNReal.ofReal F⁻¹ * ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) := by
        rw [← ENNReal.ofReal_mul hFinv, mul_inv, mul_assoc]
      _ ≤ ENNReal.ofReal F⁻¹ *
          volume.withDensity (fun z => ENNReal.ofReal (b0 z)) (Metric.ball x r) :=
        mul_le_mul_right hlo _
      _ ≤ _ := hml
  · calc
      _ ≤ ENNReal.ofReal F *
          volume.withDensity (fun z => ENNReal.ofReal (b0 z)) (Metric.ball x r) := hmu
      _ ≤ ENNReal.ofReal F * ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)) :=
        mul_le_mul_right hup _
      _ = _ := by rw [← ENNReal.ofReal_mul hF0, mul_assoc]

end SubdiffusiveProcess.Static
