import SubdiffusiveProcess.Probability.IntegratedResponseCompactness

/-! # Conditioning on a whole retained block

The retained random element need not be its total potential. A measurable
map into the potential space pushes the retained law forward. Fubini proves
that the actual conditional expectation given the whole block is the pullback
of the potential-law conditional expectation. No injectivity of that map or
equality of the two conditioning sigma fields is assumed.
-/

open MeasureTheory Filter Set
open scoped ENNReal MeasureTheory
noncomputable section
namespace SubdiffusiveProcess
variable {A X Y : Type*} [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure A} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Finite moments transfer to the joint law of the retained potential and discarded block. -/
theorem memLp_retained_response_law {V : A → X} (hV : Measurable V)
    {f : X × Y → ℝ} (hm : Measurable f) {q : ℝ≥0∞}
    (hf : MemLp (fun p : A × Y => f (V p.1, p.2)) q (μ.prod ν)) :
    MemLp f q ((μ.map V).prod ν) := by
  have he := (hV.measurePreserving μ).prod (MeasurePreserving.id ν)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [← eLpNorm_comp_measurePreserving hm.aestronglyMeasurable he]
  exact hf.2

/-- Conditioning on the whole retained block agrees with the potential-law average, almost everywhere. -/
theorem condExp_retained_response_law {V : A → X} (hV : Measurable V)
    {f : X × Y → ℝ} (hm : Measurable f)
    (hf : Integrable (fun p : A × Y => f (V p.1, p.2)) (μ.prod ν)) :
    (μ.prod ν)[(fun p : A × Y => f (V p.1, p.2)) |
      (inferInstance : MeasurableSpace A).comap Prod.fst] =ᵐ[μ.prod ν]
      fun p => ((μ.map V).prod ν)[f |
        (inferInstance : MeasurableSpace X).comap Prod.fst] (V p.1, p.2) := by
  haveI : IsProbabilityMeasure (μ.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  have he := (hV.measurePreserving μ).prod (MeasurePreserving.id ν)
  have hfi : Integrable f ((μ.map V).prod ν) :=
    (he.integrable_comp hm.aestronglyMeasurable).mp hf
  have hleft := condExp_prod_fst_integral hf
  have hright := he.quasiMeasurePreserving.ae_eq (condExp_prod_fst_integral hfi)
  exact hleft.trans hright.symm

/-- Compactness of conditional responses given the whole retained block, from original moments. -/
theorem retained_conditional_responses_isCompact_closure
    [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X]
    {V : A → X} (hV : Measurable V) {ι : Type*} {f : ι → X × Y → ℝ}
    (hm : ∀ i, Measurable (f i)) (hn : ∀ i x y, 0 ≤ f i (x, y))
    {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i x x' y, f i (x, y) ≤ Real.exp (C * dist x x') * f i (x', y))
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hqt : q ≠ ∞)
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hf : ∀ i, MemLp (fun a : A × Y => f i (V a.1, a.2)) q (μ.prod ν))
    (hb : ∀ i, eLpNorm (fun a : A × Y => f i (V a.1, a.2)) q (μ.prod ν) ≤ B) :
    IsCompact (closure (range (fun i =>
      (memLp_condExp_prod_fst hp.out (ne_top_of_lt hpq) ((hf i).mono_exponent hpq.le)).toLp
        ((μ.prod ν)[(fun a : A × Y => f i (V a.1, a.2)) |
          (inferInstance : MeasurableSpace A).comap Prod.fst])))) := by
  haveI : IsProbabilityMeasure (μ.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  have he := (hV.measurePreserving μ).prod (MeasurePreserving.id ν)
  have hfi := fun i => memLp_retained_response_law hV (hm i) (hf i)
  have hbi : ∀ i, eLpNorm (f i) q ((μ.map V).prod ν) ≤ B := by
    intro i
    rw [← eLpNorm_comp_measurePreserving (hm i).aestronglyMeasurable he]
    exact hb i
  have hcompact := conditional_responses_isCompact_closure hm hn hC hc hpq hqt hB hfi hbi
  let e := Lp.compMeasurePreserving (E := ℝ) (p := p) (Prod.map V id) he
  have heiso : Isometry e := Lp.isometry_compMeasurePreserving he
  have hrep : (fun i =>
      (memLp_condExp_prod_fst hp.out (ne_top_of_lt hpq) ((hf i).mono_exponent hpq.le)).toLp
        ((μ.prod ν)[(fun a : A × Y => f i (V a.1, a.2)) |
          (inferInstance : MeasurableSpace A).comap Prod.fst])) =
      e ∘ (fun i =>
        (memLp_condExp_prod_fst hp.out (ne_top_of_lt hpq) ((hfi i).mono_exponent hpq.le)).toLp
          (((μ.map V).prod ν)[f i |
            (inferInstance : MeasurableSpace X).comap Prod.fst])) := by
    funext i
    apply Lp.ext
    exact ((memLp_condExp_prod_fst hp.out (ne_top_of_lt hpq)
      ((hf i).mono_exponent hpq.le)).coeFn_toLp.trans
      (condExp_retained_response_law hV (hm i) ((hf i).integrable (hp.out.trans hpq.le)))).trans
      ((Lp.coeFn_compMeasurePreserving _ he).trans
        (he.quasiMeasurePreserving.ae_eq (memLp_condExp_prod_fst hp.out
          (ne_top_of_lt hpq) ((hfi i).mono_exponent hpq.le)).coeFn_toLp)).symm
  rw [hrep, Set.range_comp e,
    heiso.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous heiso.continuous]
  exact hcompact.image heiso.continuous

end SubdiffusiveProcess
