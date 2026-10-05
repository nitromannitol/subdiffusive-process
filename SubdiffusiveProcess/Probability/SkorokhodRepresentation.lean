module

public import SubdiffusiveProcess.Probability.CompactQuantile
public import SubdiffusiveProcess.Probability.NullFrontierCoding
public import SubdiffusiveProcess.Probability.AlmostContinuousMapping
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

@[expose] public section

/-! Skorokhod representation via a continuity-set code and a common quantile source. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
universe u
namespace SubdiffusiveProcess.Probability

theorem skorokhod_representation
    {X : Type u} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (h : Tendsto μ atTop (𝓝 ν)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (Xn : ℕ → Ω → X) (X0 : Ω → X),
      IsProbabilityMeasure P ∧ (∀ n, Measurable (Xn n)) ∧ Measurable X0 ∧
      (∀ n, P.map (Xn n) = (μ n : Measure X)) ∧ P.map X0 = (ν : Measure X) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => Xn n ω) atTop (𝓝 (X0 ω)) := by
  classical
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have hX : (univ : Set X).Nonempty :=
    nonempty_of_measure_ne_zero (show (ν : Measure X) univ ≠ 0 by norm_num [measure_univ])
  let : Nonempty X := ⟨hX.choose⟩
  obtain ⟨e, he, heI, hec, het⟩ := exists_null_frontier_real_coding (ν : Measure X)
  let R : ProbabilityMeasure X → ProbabilityMeasure ℝ := fun ρ => ρ.map e
  have hsupp : ∀ ρ, (R ρ : Measure ℝ) (Icc (0 : ℝ) 1) = 1 := by
    intro ρ
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply he.measurable measurableSet_Icc]
    have hepre : e ⁻¹' Icc (0 : ℝ) 1 = univ := preimage_eq_univ_iff.mpr (by rintro _ ⟨x, rfl⟩; exact heI x)
    rw [hepre, measure_univ]
  let Q : ProbabilityMeasure X → ℝ → ℝ := fun ρ => compactQuantile (R ρ : Measure ℝ)
  have hQm : ∀ ρ, Measurable (Q ρ) := fun ρ => measurable_compactQuantile (hsupp ρ)
  have hQlaw : ∀ ρ, quantileSource.map (Q ρ) = (ρ : Measure X).map e := by
    intro ρ
    exact map_compactQuantile (hsupp ρ)
  let Y : ProbabilityMeasure X → ℝ → X := fun ρ => he.invFun ∘ Q ρ
  have hYm : ∀ ρ, Measurable (Y ρ) := fun ρ => he.measurable_invFun.comp (hQm ρ)
  have hYlaw : ∀ ρ, quantileSource.map (Y ρ) = (ρ : Measure X) := by
    intro ρ
    change quantileSource.map (he.invFun ∘ Q ρ) = (ρ : Measure X)
    rw [← Measure.map_map he.measurable_invFun (hQm ρ), hQlaw ρ,
      Measure.map_map he.measurable_invFun he.measurable]
    have hi : he.invFun ∘ e = id := funext he.leftInverse_invFun
    rw [hi, Measure.map_id]
  have hcodeY : ∀ ρ, ∀ᵐ u ∂quantileSource, e (Y ρ u) = Q ρ u := by
    intro ρ
    have hr : ∀ᵐ v ∂quantileSource.map (Q ρ), v ∈ range e := by
      rw [hQlaw ρ]
      exact ae_map_mem_range he.measurableSet_range (μ := (ρ : Measure X)) he.measurable.aemeasurable
    have hr' := (ae_map_iff (hQm ρ).aemeasurable he.measurableSet_range).mp hr
    filter_upwards [hr'] with u hu
    obtain ⟨x, hx⟩ := hu
    change e (he.invFun (Q ρ u)) = Q ρ u
    rw [← hx, he.leftInverse_invFun]
  have hconvQ : ∀ᵐ u ∂quantileSource, Tendsto (fun n => Q (μ n) u) atTop (𝓝 (Q ν u)) :=
    tendsto_compactQuantile (fun n => hsupp (μ n)) (hsupp ν)
      (tendsto_map_of_ae_continuousAt he.measurable hec h)
  have hconvY : ∀ᵐ u ∂quantileSource, Tendsto (fun n => Y (μ n) u) atTop (𝓝 (Y ν u)) := by
    filter_upwards [hconvQ, ae_all_iff.mpr (fun n => hcodeY (μ n)), hcodeY ν] with u hu hn h0
    apply het
    simpa only [Function.comp_def, hn, h0] using hu
  let Ω := (ℕ → X) × X
  let Φ : ℝ → Ω := fun u => (fun n => Y (μ n) u, Y ν u)
  have hΦ : Measurable Φ := (measurable_pi_iff.mpr (fun n => hYm (μ n))).prodMk (hYm ν)
  let P : Measure Ω := quantileSource.map Φ
  let Xn : ℕ → Ω → X := fun n ω => ω.1 n
  let X0 : Ω → X := Prod.snd
  have hXn : ∀ n, Measurable (Xn n) := fun n => (measurable_pi_apply n).comp measurable_fst
  have hX0 : Measurable X0 := measurable_snd
  have hP : IsProbabilityMeasure P := inferInstance
  refine ⟨Ω, inferInstance, P, Xn, X0, hP, hXn, hX0, ?_, ?_, ?_⟩
  · intro n
    rw [Measure.map_map (hXn n) hΦ]
    exact hYlaw (μ n)
  · rw [Measure.map_map hX0 hΦ]
    exact hYlaw ν
  · have hT : MeasurableSet {ω : Ω | Tendsto (fun n => Xn n ω) atTop (𝓝 (X0 ω))} := by
      have hset : {ω : Ω | Tendsto (fun n => Xn n ω) atTop (𝓝 (X0 ω))} =
          {ω | Tendsto (fun n => dist (Xn n ω) (X0 ω)) atTop (𝓝 (0 : ℝ))} := by
        ext ω
        exact tendsto_iff_dist_tendsto_zero
      rw [hset]
      exact measurableSet_tendsto (𝓝 (0 : ℝ)) (fun n => (hXn n).dist hX0)
    exact (ae_map_iff hΦ.aemeasurable hT).mpr hconvY

end SubdiffusiveProcess.Probability
