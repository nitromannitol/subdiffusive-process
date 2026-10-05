module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-! # Absolute convergence from summable expected norms

This is the Tonelli step in the infrared construction. The summability set
is measurable and has full measure; restricting the law to it preserves the
original measure. The sum itself will only be defined on that summability
carrier, so no arbitrary value is assigned to a divergent environment.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal MeasureTheory
namespace SubdiffusiveProcess
variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]

/-- Summable expected norms imply almost-everywhere absolute summability. -/
theorem ae_summable_norm_of_summable_integral_norm {μ : Measure A} {F : ℕ → A → E}
    (hf : ∀ n, Integrable (F n) μ) (hs : Summable (fun n => ∫ a, ‖F n a‖ ∂μ)) :
    ∀ᵐ a ∂μ, Summable (fun n => ‖F n a‖) := by
  have hm n : AEMeasurable (fun a => ‖F n a‖ₑ) μ := (hf n).1.enorm
  have hfin : (∫⁻ a, ∑' n, ‖F n a‖ₑ ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hf _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun a => norm_nonneg (F n a))) hs]
    exact ENNReal.ofReal_ne_top
  refine (ae_lt_top' (AEMeasurable.tsum hm) hfin).mono ?_
  intro a ha
  change Summable (fun n => (‖F n a‖₊ : ℝ))
  rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact ha.ne

variable [MeasurableSpace E] [BorelSpace E]

/-- Absolute summability is a measurable condition on the original random coordinates. -/
theorem measurableSet_summable_norm {F : ℕ → A → E} (hf : ∀ n, Measurable (F n)) :
    MeasurableSet {a | Summable (fun n => ‖F n a‖)} := by
  have hset : {a | Summable (fun n => ‖F n a‖)} =
      {a | (∑' n, ‖F n a‖ₑ) ≠ ∞} := by
    ext a
    change Summable (fun n => (‖F n a‖₊ : ℝ)) ↔ _
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.symm
  rw [hset]
  exact (measurableSet_eq_fun (Measurable.tsum (fun n => (hf n).enorm)) measurable_const).compl

/-- Removing only the nonsummable null set preserves the entire environment law. -/
theorem measurePreserving_summable_norm_subtype {μ : Measure A} {F : ℕ → A → E}
    (hm : ∀ n, Measurable (F n)) (hf : ∀ n, Integrable (F n) μ)
    (hs : Summable (fun n => ∫ a, ‖F n a‖ ∂μ)) :
    MeasurePreserving
      (Subtype.val : {a // Summable (fun n => ‖F n a‖)} → A)
      (μ.comap Subtype.val) μ := by
  refine ⟨measurable_subtype_coe, ?_⟩
  exact (map_comap_subtype_coe (μ := μ) (s := {a | Summable (fun n => ‖F n a‖)})
    (measurableSet_summable_norm hm)).trans
      (Measure.restrict_eq_self_of_ae_mem (ae_summable_norm_of_summable_integral_norm hf hs))

/-- The summable-environment subtype carries the original probability law. -/
theorem isProbabilityMeasure_summable_norm_comap {μ : Measure A} [IsProbabilityMeasure μ]
    {F : ℕ → A → E} (hm : ∀ n, Measurable (F n)) (hf : ∀ n, Integrable (F n) μ)
    (hs : Summable (fun n => ∫ a, ‖F n a‖ ∂μ)) :
    IsProbabilityMeasure (μ.comap (Subtype.val : {a // Summable (fun n => ‖F n a‖)} → A)) := by
  have he := measurePreserving_summable_norm_subtype hm hf hs
  have : IsProbabilityMeasure ((μ.comap
      (Subtype.val : {a // Summable (fun n => ‖F n a‖)} → A)).map Subtype.val) :=
    he.map_eq.symm ▸ inferInstance
  exact Measure.isProbabilityMeasure_of_map he.measurable.aemeasurable

end SubdiffusiveProcess
