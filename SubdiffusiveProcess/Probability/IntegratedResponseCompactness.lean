import SubdiffusiveProcess.Probability.IntegratedResponseComparison
import SubdiffusiveProcess.Probability.ResponseCompactness

/-! # Compactness of actual conditional response averages

The higher moment is imposed on the original product response. Averaging
contracts that moment, so it is not separately assumed for the conditional
mean. The conclusion is compact closure of Mathlib's actual conditional
expectations in the product-environment Lp space.
-/

open MeasureTheory Filter Set
open scoped ENNReal MeasureTheory
noncomputable section
namespace SubdiffusiveProcess
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
/-- The averaged response has no larger finite moment on the retained coordinate. -/
theorem eLpNorm_integral_fiber_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : X × Y → ℝ} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    eLpNorm (fun x => ∫ y, f (x, y) ∂ν) p μ ≤ eLpNorm f p (μ.prod ν) := by
  have hm := hf.integral_prod_right'
  rw [← eLpNorm_comp_measurePreserving hm (measurePreserving_fst (μ := μ) (ν := ν))]
  exact eLpNorm_prod_integral_le hp hpt hf

omit [IsProbabilityMeasure μ] in
/-- Finite moments of the original response supply finite moments of its actual average. -/
theorem memLp_integral_fiber {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : X × Y → ℝ} (hf : MemLp f p (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x, y) ∂ν) p μ :=
  ⟨hf.1.integral_prod_right', (eLpNorm_integral_fiber_le hp hpt hf.1).trans_lt hf.2⟩

/-- The first-coordinate conditional expectation has every prescribed finite moment of the input. -/
theorem memLp_condExp_prod_fst {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : X × Y → ℝ} (hf : MemLp f p (μ.prod ν)) :
    MemLp ((μ.prod ν)[f | (inferInstance : MeasurableSpace X).comap Prod.fst]) p (μ.prod ν) := by
  have ha := (memLp_integral_fiber hp hpt hf).comp_measurePreserving
    (measurePreserving_fst (μ := μ) (ν := ν))
  exact ha.ae_eq (condExp_prod_fst_integral (hf.integrable hp)).symm

/-- The conditional-expectation Lp class equals the pullback of its integral representative. -/
theorem condExp_prod_fst_toLp_eq {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpt : p ≠ ∞)
    {f : X × Y → ℝ} (hf : MemLp f p (μ.prod ν)) :
    (memLp_condExp_prod_fst hp.out hpt hf).toLp
      ((μ.prod ν)[f | (inferInstance : MeasurableSpace X).comap Prod.fst]) =
    Lp.compMeasurePreserving Prod.fst (measurePreserving_fst (μ := μ) (ν := ν))
      ((memLp_integral_fiber hp.out hpt hf).toLp (fun x => ∫ y, f (x, y) ∂ν)) := by
  apply Lp.ext
  exact ((memLp_condExp_prod_fst hp.out hpt hf).coeFn_toLp.trans
    (condExp_prod_fst_integral (hf.integrable hp.out))).trans
    ((Lp.coeFn_compMeasurePreserving _ (measurePreserving_fst (μ := μ) (ν := ν))).trans
      ((measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae_eq
        (memLp_integral_fiber hp.out hpt hf).coeFn_toLp)).symm

variable [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X]

/-- The actual averaged response family is compact in smaller Lp, from original higher moments. -/
theorem integrated_responses_isCompact_closure {ι : Type*} {f : ι → X × Y → ℝ}
    (hm : ∀ i, Measurable (f i)) (hn : ∀ i x y, 0 ≤ f i (x, y))
    {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i x x' y, f i (x, y) ≤ Real.exp (C * dist x x') * f i (x', y))
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hqt : q ≠ ∞)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hf : ∀ i, MemLp (f i) q (μ.prod ν))
    (hb : ∀ i, eLpNorm (f i) q (μ.prod ν) ≤ K) :
    IsCompact (closure (range (fun i =>
      ((memLp_integral_fiber (hp.out.trans hpq.le) hqt (hf i)).mono_exponent hpq.le).toLp
        (fun x => ∫ y, f i (x, y) ∂ν)))) := by
  exact law_responses_isCompact_closure μ hC
    (fun i x _ => integral_nonneg (hn i x))
    (fun i x _ x' _ => integrated_response_comparison (hm i)
      ((hf i).integrable (hp.out.trans hpq.le)) (hn i) (hc i) x x')
    hpq hqt hK (fun i => memLp_integral_fiber (hp.out.trans hpq.le) hqt (hf i))
    (fun i => (eLpNorm_integral_fiber_le (hp.out.trans hpq.le) hqt (hf i).1).trans (hb i))

/-- Compact closure of the actual conditional expectations in the product environment Lp. -/
theorem conditional_responses_isCompact_closure {ι : Type*} {f : ι → X × Y → ℝ}
    (hm : ∀ i, Measurable (f i)) (hn : ∀ i x y, 0 ≤ f i (x, y))
    {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i x x' y, f i (x, y) ≤ Real.exp (C * dist x x') * f i (x', y))
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hqt : q ≠ ∞)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hf : ∀ i, MemLp (f i) q (μ.prod ν))
    (hb : ∀ i, eLpNorm (f i) q (μ.prod ν) ≤ K) :
    IsCompact (closure (range (fun i =>
      (memLp_condExp_prod_fst hp.out (ne_top_of_lt hpq) ((hf i).mono_exponent hpq.le)).toLp
        ((μ.prod ν)[f i | (inferInstance : MeasurableSpace X).comap Prod.fst])))) := by
  have ha := integrated_responses_isCompact_closure hm hn hC hc hpq hqt hK hf hb
  let e := Lp.compMeasurePreserving (E := ℝ) (p := p) Prod.fst (measurePreserving_fst (μ := μ) (ν := ν))
  have he : Isometry e := Lp.isometry_compMeasurePreserving (measurePreserving_fst (μ := μ) (ν := ν))
  have hrep : (fun i =>
      (memLp_condExp_prod_fst hp.out (ne_top_of_lt hpq) ((hf i).mono_exponent hpq.le)).toLp
        ((μ.prod ν)[f i | (inferInstance : MeasurableSpace X).comap Prod.fst])) =
      e ∘ (fun i => ((memLp_integral_fiber (hp.out.trans hpq.le) hqt (hf i)).mono_exponent hpq.le).toLp
        (fun x => ∫ y, f i (x, y) ∂ν)) := by
    funext i
    exact condExp_prod_fst_toLp_eq (ne_top_of_lt hpq) ((hf i).mono_exponent hpq.le)
  rw [hrep, Set.range_comp e,
    he.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous he.continuous]
  exact ha.image he.continuous

end SubdiffusiveProcess
