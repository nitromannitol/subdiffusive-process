module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
# The actual law restricted to its support

Source: Lemma 32, `lem:conditional-compact`. The comap along the support
subtype preserves the original law, is a probability measure when the
original law is one, and is positive on nonempty relative open sets.
These facts are derived, not extra assumptions on the potential ensemble.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace SubdiffusiveProcess

/-- Passing to the actual support preserves the probability law. -/
theorem measurePreserving_support_subtype {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) :
    MeasurePreserving (Subtype.val : μ.support → X) (μ.comap Subtype.val) μ := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [map_comap_subtype_coe μ.isClosed_support.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem μ.support_mem_ae

/-- The induced law on the support is a probability measure. -/
theorem isProbabilityMeasure_support_comap {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.comap (Subtype.val : μ.support → X)) := by
  have he := measurePreserving_support_subtype μ
  have : IsProbabilityMeasure ((μ.comap (Subtype.val : μ.support → X)).map Subtype.val) :=
    he.map_eq.symm ▸ inferInstance
  exact Measure.isProbabilityMeasure_of_map he.measurable.aemeasurable

/-- The support law is positive on every nonempty relatively open set. -/
theorem isOpenPosMeasure_support_comap {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) :
    (μ.comap (Subtype.val : μ.support → X)).IsOpenPosMeasure := by
  refine ⟨fun U hU hUne => ?_⟩
  obtain ⟨V, hV, hUV⟩ := isOpen_induced_iff.mp hU
  obtain ⟨x, hx⟩ := hUne
  have hxV : (x : X) ∈ V := by rw [← hUV] at hx; exact hx
  have hpos : 0 < μ V :=
    (Measure.mem_support_iff_forall x.val).mp x.property V (hV.mem_nhds hxV)
  have he := measurePreserving_support_subtype μ
  rw [← hUV]
  rw [← he.map_eq, Measure.map_apply he.measurable hV.measurableSet] at hpos
  exact hpos.ne'

end SubdiffusiveProcess
