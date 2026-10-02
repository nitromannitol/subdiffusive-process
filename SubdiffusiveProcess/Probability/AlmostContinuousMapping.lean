import Mathlib.MeasureTheory.Measure.Portmanteau

/-! A continuous mapping theorem with continuity almost everywhere under the limiting law. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace SubdiffusiveProcess.Probability

theorem tendsto_map_of_ae_continuousAt {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    {f : X → Y} (hf : Measurable f) (hc : ∀ᵐ x ∂(ν : Measure X), ContinuousAt f x)
    (h : Tendsto μ atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map hf.aemeasurable) atTop (𝓝 (ν.map hf.aemeasurable)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro C hC
  have heq : (ν : Measure X) (closure (f ⁻¹' C)) = (ν : Measure X) (f ⁻¹' C) := by
    apply measure_congr
    filter_upwards [hc] with x hx
    apply propext
    change x ∈ closure (f ⁻¹' C) ↔ f x ∈ C
    constructor
    · intro hxc
      have hfc := mem_closure_image hx hxc
      exact hC.closure_eq ▸ closure_mono (image_preimage_subset f C) hfc
    · exact fun hxc => subset_closure hxc
  simp only [ProbabilityMeasure.toMeasure_map, Measure.map_apply hf hC.measurableSet]
  calc
    limsup (fun n => (μ n : Measure X) (f ⁻¹' C)) atTop
        ≤ limsup (fun n => (μ n : Measure X) (closure (f ⁻¹' C))) atTop :=
      limsup_le_limsup (Eventually.of_forall (fun n => measure_mono subset_closure))
    _ ≤ (ν : Measure X) (closure (f ⁻¹' C)) :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h isClosed_closure
    _ = (ν : Measure X) (f ⁻¹' C) := heq

end SubdiffusiveProcess.Probability
