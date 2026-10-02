import SubdiffusiveProcess.Compactness.PointwiseExtraction
import SubdiffusiveProcess.Compactness.SequentialCompactness
import SubdiffusiveProcess.Probability.SupportLaw
import SubdiffusiveProcess.Probability.ResponseContinuity
import SubdiffusiveProcess.Probability.HigherMomentConvergence

/-!
# Conditional-response compactness

Source: Lemma 32, E043, `lem:conditional-compact`. For every finite
1 <= p < q, a uniform q moment and the multiplicative potential comparison
on the actual law support imply compact closure of the random responses
in Lp. The proof uses a dense-set extraction and higher-moment convergence;
no compact exhaustion or tightness hypothesis on the parameter space is
needed. The quantitative band bounds and full Proposition 33 remain
separate model obligations.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace SubdiffusiveProcess

/-- Conditional-response compactness on the support of a potential law.
Only the strictly higher moment q is required; the parameter space need not be complete. -/
theorem exp_comparison_responses_subseq_Lp {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] {f : ℕ → X → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hn : ∀ n x, 0 ≤ f n x)
    (hcmp : ∀ n x y, f n x ≤ Real.exp (C * dist x y) * f n y)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p < q) (hq : q ≠ ∞)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hf : ∀ n, MemLp (f n) q μ)
    (hb : ∀ n, eLpNorm (f n) q μ ≤ K) :
    ∃ (g : X → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Continuous g ∧ MemLp g q μ ∧
      (∀ x, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x))) ∧
      Tendsto (fun n => eLpNorm (f (φ n) - g) p μ) atTop (𝓝 0) := by
  have hb1 : ∀ n, eLpNorm (f n) 1 μ ≤ K := fun n =>
    (eLpNorm_le_eLpNorm_of_exponent_le (hp.trans hpq.le) (hf n).1).trans (hb n)
  have hpoint := pointwise_bound_of_exp_comparison hC hn hcmp hK hb1
  have heq := equicontinuous_of_exp_comparison hC hn hcmp hpoint
  obtain ⟨g, φ, hφ, hg, hlim⟩ := exists_pointwise_subseq_of_equicontinuous heq
    (fun x => by
      obtain ⟨M, hM⟩ := hpoint x
      exact ⟨M, fun n => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn n x)] using hM n⟩)
  have hLp := tendsto_eLpNorm_of_ae_tendsto_of_higher_bound hp hpq hq hK
    (fun n => (hf (φ n)).1) hg.aestronglyMeasurable (fun n => hb (φ n))
    (Eventually.of_forall hlim)
  exact ⟨g, φ, hφ, hg, hLp.1, hlim, hLp.2⟩


/-- The positive response family has compact closure in the actual Lp space. -/
theorem exp_comparison_responses_isCompact_closure {X ι : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] {f : ι → X → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hn : ∀ i x, 0 ≤ f i x)
    (hcmp : ∀ i x y, f i x ≤ Real.exp (C * dist x y) * f i y)
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hq : q ≠ ∞)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hf : ∀ i, MemLp (f i) q μ)
    (hb : ∀ i, eLpNorm (f i) q μ ≤ K) :
    IsCompact (closure (range (fun i => ((hf i).mono_exponent hpq.le).toLp (f i)))) := by
  classical
  apply isCompact_closure_of_subseq_tendsto
  intro u hu
  choose I hI using hu
  obtain ⟨g, φ, hφ, _, hgq, _, hlim⟩ := exp_comparison_responses_subseq_Lp hC
    (fun n => hn (I n)) (fun n => hcmp (I n)) hp.out hpq hq hK
    (fun n => hf (I n)) (fun n => hb (I n))
  have hgp := hgq.mono_exponent hpq.le
  refine ⟨hgp.toLp g, φ, hφ, ?_⟩
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => f (I (φ n)))
    (fun n => (hf (I (φ n))).mono_exponent hpq.le) g hgp).mpr hlim
  convert ht using 1
  funext n
  exact (hI (φ n)).symm

/-- Lemma 32 on the support of an arbitrary Borel potential law.
The support law is constructed, with probability and full support proved internally. -/
theorem support_responses_isCompact_closure {X ι : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : ι → μ.support → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hn : ∀ i x, 0 ≤ f i x)
    (hcmp : ∀ i x y, f i x ≤ Real.exp (C * dist x y) * f i y)
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hq : q ≠ ∞)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hf : ∀ i, MemLp (f i) q (μ.comap Subtype.val))
    (hb : ∀ i, eLpNorm (f i) q (μ.comap Subtype.val) ≤ K) :
    IsCompact (closure (range (fun i =>
      (show MemLp (f i) p (μ.comap Subtype.val) from
        (hf i).mono_exponent hpq.le).toLp (f i)))) := by
  haveI : IsProbabilityMeasure (μ.comap (Subtype.val : μ.support → X)) :=
    isProbabilityMeasure_support_comap μ
  haveI : (μ.comap (Subtype.val : μ.support → X)).IsOpenPosMeasure :=
    isOpenPosMeasure_support_comap μ
  haveI : Nonempty μ.support := ⟨⟨(μ.nonempty_support (IsProbabilityMeasure.ne_zero μ)).choose,
    (μ.nonempty_support (IsProbabilityMeasure.ne_zero μ)).choose_spec⟩⟩
  exact exp_comparison_responses_isCompact_closure hC hn hcmp hpq hq hK hf hb


/-- Lemma 32 for a general potential law; comparison is needed only on its support. -/
theorem law_responses_isCompact_closure {X ι : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : ι → X → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hn : ∀ i x, x ∈ μ.support → 0 ≤ f i x)
    (hcmp : ∀ i x, x ∈ μ.support → ∀ y, y ∈ μ.support →
      f i x ≤ Real.exp (C * dist x y) * f i y)
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hq : q ≠ ∞)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hf : ∀ i, MemLp (f i) q μ)
    (hb : ∀ i, eLpNorm (f i) q μ ≤ K) :
    IsCompact (closure (range (fun i => ((hf i).mono_exponent hpq.le).toLp (f i)))) := by
  have hV := measurePreserving_support_subtype μ
  let ν := μ.comap (Subtype.val : μ.support → X)
  let g := fun i (x : μ.support) => f i x.val
  have hgm : ∀ i, MemLp (g i) q ν := fun i => (hf i).comp_measurePreserving hV
  have hgb : ∀ i, eLpNorm (g i) q ν ≤ K := fun i => by
    change eLpNorm (f i ∘ (Subtype.val : μ.support → X)) q (μ.comap Subtype.val) ≤ K
    rw [eLpNorm_comp_measurePreserving (hf i).1 hV]
    exact hb i
  have hc := support_responses_isCompact_closure μ hC
    (fun i x => hn i x.val x.property)
    (fun i x y => hcmp i x.val x.property y.val y.property) hpq hq hK hgm hgb
  let e : Lp ℝ p μ →+ Lp ℝ p ν := Lp.compMeasurePreserving Subtype.val hV
  have he : Isometry e := Lp.isometry_compMeasurePreserving hV
  rw [he.isClosedEmbedding.isEmbedding.closure_eq_preimage_closure_image]
  apply he.isClosedEmbedding.isCompact_preimage
  rw [← range_comp']
  exact hc


/-- The law-space compactness conclusion holds for the original random responses f_i(V). -/
theorem random_potential_responses_isCompact_closure {Ω X ι : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (V : Ω → X) (hV : Measurable V)
    {f : ι → X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hn : ∀ i x, x ∈ (P.map V).support → 0 ≤ f i x)
    (hcmp : ∀ i x, x ∈ (P.map V).support → ∀ y, y ∈ (P.map V).support →
      f i x ≤ Real.exp (C * dist x y) * f i y)
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hq : q ≠ ∞)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hf : ∀ i, MemLp (f i) q (P.map V))
    (hb : ∀ i, eLpNorm (f i) q (P.map V) ≤ K) :
    IsCompact (closure (range (fun i =>
      (((hf i).mono_exponent hpq.le).comp_measurePreserving (hV.measurePreserving P)).toLp
        (f i ∘ V)))) := by
  haveI : IsProbabilityMeasure (P.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  have hc := law_responses_isCompact_closure (P.map V) hC hn hcmp hpq hq hK hf hb
  let e := Lp.compMeasurePreserving (E := ℝ) (p := p) V (hV.measurePreserving P)
  have he : Isometry e := Lp.isometry_compMeasurePreserving (hV.measurePreserving P)
  change IsCompact (closure (range (fun i => e (((hf i).mono_exponent hpq.le).toLp (f i)))))
  rw [range_comp', he.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous he.continuous]
  exact hc.image he.continuous

end SubdiffusiveProcess
