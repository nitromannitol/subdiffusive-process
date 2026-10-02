import SubdiffusiveProcess.Section10.PhysicalTightnessContainment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Expected majorants after restricting an integrable random exit constant
to a deterministic threshold. The bounded family need not be measurable in
its uncountable starting-point parameter. -/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- A quenched estimate on `F<=K` has an all-environment measurable majorant.
Its expectation costs the containment bound, the deterministic error, and
the Markov tail `C/K`. No measurable supremum over starts is assumed. -/
theorem measurable_majorant_of_integrable_good_event {Ω Z : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Set Z) (f : Ω → Z → ENNReal) (hprob : ∀ omega x, f omega x ≤ 1)
    (F : Ω → ℝ) (hF : Measurable F) (C K epsilon : ℝ)
    (hC : 0 ≤ C) (hK : 0 < K) (hepsilon : 0 ≤ epsilon)
    (hFint : (∫⁻ omega, ENNReal.ofReal (F omega) ∂μ) ≤ ENNReal.ofReal C)
    (G : Ω → ENNReal) (hG : Measurable G)
    (hGint : (∫⁻ omega, G omega ∂μ) ≤ ENNReal.ofReal epsilon)
    (hgood : ∀ᵐ omega ∂μ, ∀ x ∈ B, F omega ≤ K →
      f omega x ≤ G omega + ENNReal.ofReal epsilon) :
    ∃ Gout : Ω → ENNReal, Measurable Gout ∧
      (∀ omega, ∀ x ∈ B, f omega x ≤ Gout omega) ∧
      (∫⁻ omega, Gout omega ∂μ) ≤ ENNReal.ofReal (2 * epsilon + C / K) := by
  classical
  let bad : Set Ω := {omega | K < F omega}
  have hbad : MeasurableSet bad := measurableSet_lt measurable_const hF
  have htail : μ bad ≤ ENNReal.ofReal (C / K) := by
    have hthreshold : ENNReal.ofReal K ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hK)
    calc
      μ bad ≤ μ {omega | ENNReal.ofReal K ≤ ENNReal.ofReal (F omega)} :=
        measure_mono fun omega homega => ENNReal.ofReal_le_ofReal homega.le
      _ ≤ (∫⁻ omega, ENNReal.ofReal (F omega) ∂μ) / ENNReal.ofReal K :=
        meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hF).aemeasurable
          hthreshold ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C / ENNReal.ofReal K := ENNReal.div_le_div_right hFint _
      _ = ENNReal.ofReal (C / K) := by rw [ENNReal.ofReal_div_of_pos hK]
  let g : Ω → ENNReal := fun omega =>
    G omega + ENNReal.ofReal epsilon + bad.indicator (fun _ => 1) omega
  have hg : Measurable g := (hG.add measurable_const).add
    (measurable_const.indicator hbad)
  have hgpoint : ∀ᵐ omega ∂μ, ∀ x ∈ B, f omega x ≤ g omega := by
    filter_upwards [hgood] with omega homega
    intro x hx
    by_cases hb : omega ∈ bad
    · simpa only [g, indicator_of_mem hb] using
        (hprob omega x).trans (le_add_of_nonneg_left (zero_le _))
    · have hFK : F omega ≤ K := le_of_not_gt hb
      simpa only [g, indicator_of_notMem hb, add_zero] using homega x hx hFK
  have hgint : (∫⁻ omega, g omega ∂μ) ≤ ENNReal.ofReal (2 * epsilon + C / K) := by
    simp only [g]
    rw [lintegral_add_left (hG.add measurable_const), lintegral_add_left hG,
      lintegral_const, measure_univ, mul_one, lintegral_indicator hbad]
    simp only [setLIntegral_const, one_mul]
    calc
      (∫⁻ omega, G omega ∂μ) + ENNReal.ofReal epsilon + μ bad ≤
          ENNReal.ofReal epsilon + ENNReal.ofReal epsilon + ENNReal.ofReal (C / K) := by
        gcongr
      _ = ENNReal.ofReal (2 * epsilon + C / K) := by
        rw [← ENNReal.ofReal_add hepsilon hepsilon,
          ← ENNReal.ofReal_add (add_nonneg hepsilon hepsilon) (div_nonneg hC hK.le)]
        congr 1
        ring
  obtain ⟨Gout, hGout, hGoutpoint, hGoutint⟩ :=
    measurable_majorant_of_ae μ B f g hg hgpoint hprob
  exact ⟨Gout, hGout, hGoutpoint, hGoutint.trans_le hgint⟩

end SubdiffusiveProcess.Section10.PhysicalTightness
