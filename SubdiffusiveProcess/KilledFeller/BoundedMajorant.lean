module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.KilledFeller

/-- Clip an extended-valued probability majorant before taking its real value. -/
def boundedMajorant (a : ℝ≥0∞) : ℝ := (min a 1).toReal

theorem boundedMajorant_nonneg (a : ℝ≥0∞) : 0 ≤ boundedMajorant a := ENNReal.toReal_nonneg

theorem boundedMajorant_le_one (a : ℝ≥0∞) : boundedMajorant a ≤ 1 := by
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  simpa only [ENNReal.ofReal_one] using min_le_right a 1

theorem measurable_boundedMajorant {Ω : Type*} [MeasurableSpace Ω]
    (G : Ω → ℝ≥0∞) (hG : Measurable G) : Measurable (fun omega => boundedMajorant (G omega)) :=
  (hG.min measurable_const).ennreal_toReal

theorem integrable_boundedMajorant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (G : Ω → ℝ≥0∞) (hG : Measurable G) :
    Integrable (fun omega => boundedMajorant (G omega)) P := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_boundedMajorant G hG).aestronglyMeasurable
  exact Eventually.of_forall fun omega => by
    rw [Real.norm_of_nonneg (boundedMajorant_nonneg _)]
    exact boundedMajorant_le_one _

theorem integral_boundedMajorant_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : Ω → ℝ≥0∞) (hG : Measurable G)
    (eta : ℝ) (heta : 0 ≤ eta) (hmean : ∫⁻ omega, G omega ∂P ≤ ENNReal.ofReal eta) :
    ∫ omega, boundedMajorant (G omega) ∂P ≤ eta := by
  have hm : AEMeasurable (fun omega => min (G omega) 1) P :=
    (hG.min measurable_const).aemeasurable
  have hfin : ∀ omega, min (G omega) 1 < ⊤ := fun _ =>
    lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top
  change ∫ omega, (min (G omega) 1).toReal ∂P ≤ eta
  rw [integral_toReal hm (Eventually.of_forall hfin)]
  apply ENNReal.toReal_le_of_le_ofReal heta
  exact (lintegral_mono fun omega => min_le_left (G omega) 1).trans hmean

theorem measureReal_le_boundedMajorant {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (S : Set X) (a : ℝ≥0∞)
    (hbound : mu S ≤ a) : mu.real S ≤ boundedMajorant a := by
  apply ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top))
  exact le_min hbound prob_le_one

end SubdiffusiveProcess.KilledFeller
