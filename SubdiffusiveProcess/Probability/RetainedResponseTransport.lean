module

public import SubdiffusiveProcess.Probability.RetainedResponseCompactness

@[expose] public section

/-! # Conditional response compactness under a product decomposition

A measure-preserving equivalence is an actual relabeling of the environment.
The Lp classes below are Mathlib's conditional expectations on that original
environment, not conditional versions evaluated at hypothetical potentials.
-/

open MeasureTheory Filter Set
open scoped ENNReal MeasureTheory
noncomputable section
namespace SubdiffusiveProcess
variable {A Y Z : Type*} [MeasurableSpace A] [MeasurableSpace Y] [MeasurableSpace Z]
    {μ : Measure A} {ν : Measure Y} {P : Measure Z}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure P]

/-- Every finite input moment survives conditioning after an actual product relabeling. -/
theorem memLp_condExp_equiv_fst (e : Z ≃ᵐ A × Y)
    (he : MeasurePreserving e P (μ.prod ν)) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : Z → ℝ} (hf : MemLp f p P) :
    MemLp (P[f | (inferInstance : MeasurableSpace A).comap (fun z => (e z).1)]) p P := by
  have hfi := hf.comp_measurePreserving (he.symm e)
  have hce : P[f | (inferInstance : MeasurableSpace A).comap (fun z => (e z).1)] =ᵐ[P]
      ((μ.prod ν)[f ∘ e.symm | (inferInstance : MeasurableSpace A).comap Prod.fst]) ∘ e := by
    simpa only [MeasurableSpace.comap_comp, Function.comp_def, e.symm_apply_apply] using
      condExp_comp_measurableEquiv e he measurable_fst.comap_le (hfi.integrable hp)
  exact ((memLp_condExp_prod_fst hp hpt hfi).comp_measurePreserving he).ae_eq hce.symm

/-- The conditional-expectation Lp class is exactly transported by the relabeling. -/
theorem condExp_equiv_fst_toLp_eq (e : Z ≃ᵐ A × Y)
    (he : MeasurePreserving e P (μ.prod ν)) {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpt : p ≠ ∞)
    {f : Z → ℝ} (hf : MemLp f p P) :
    (memLp_condExp_equiv_fst e he hp.out hpt hf).toLp
      (P[f | (inferInstance : MeasurableSpace A).comap (fun z => (e z).1)]) =
    Lp.compMeasurePreserving e he
      ((memLp_condExp_prod_fst hp.out hpt (hf.comp_measurePreserving (he.symm e))).toLp
        ((μ.prod ν)[f ∘ e.symm | (inferInstance : MeasurableSpace A).comap Prod.fst])) := by
  have hfi := hf.comp_measurePreserving (he.symm e)
  have hce : P[f | (inferInstance : MeasurableSpace A).comap (fun z => (e z).1)] =ᵐ[P]
      ((μ.prod ν)[f ∘ e.symm | (inferInstance : MeasurableSpace A).comap Prod.fst]) ∘ e := by
    simpa only [MeasurableSpace.comap_comp, Function.comp_def, e.symm_apply_apply] using
      condExp_comp_measurableEquiv e he measurable_fst.comap_le (hfi.integrable hp.out)
  apply Lp.ext
  exact ((memLp_condExp_equiv_fst e he hp.out hpt hf).coeFn_toLp.trans hce).trans
    ((Lp.coeFn_compMeasurePreserving _ he).trans
      (he.quasiMeasurePreserving.ae_eq (memLp_condExp_prod_fst hp.out hpt hfi).coeFn_toLp)).symm

/-- Retained-block compactness on the original environment, assuming only original response moments. -/
theorem retained_conditional_responses_equiv_isCompact_closure
    {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (e : Z ≃ᵐ A × Y) (he : MeasurePreserving e P (μ.prod ν))
    {V : A → X} (hV : Measurable V) {ι : Type*} {f : ι → X × Y → ℝ}
    (hm : ∀ i, Measurable (f i)) (hn : ∀ i x y, 0 ≤ f i (x, y))
    {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i x x' y, f i (x, y) ≤ Real.exp (C * dist x x') * f i (x', y))
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hqt : q ≠ ∞)
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hf : ∀ i, MemLp (fun z => f i (V (e z).1, (e z).2)) q P)
    (hb : ∀ i, eLpNorm (fun z => f i (V (e z).1, (e z).2)) q P ≤ B) :
    IsCompact (closure (range (fun i =>
      (memLp_condExp_equiv_fst e he hp.out (ne_top_of_lt hpq)
        ((hf i).mono_exponent hpq.le)).toLp
        (P[(fun z => f i (V (e z).1, (e z).2)) |
          (inferInstance : MeasurableSpace A).comap (fun z => (e z).1)])))) := by
  have hfi : ∀ i, MemLp (fun a : A × Y => f i (V a.1, a.2)) q (μ.prod ν) := by
    intro i
    simpa only [Function.comp_def, e.apply_symm_apply] using
      (hf i).comp_measurePreserving (he.symm e)
  have hbi : ∀ i, eLpNorm (fun a : A × Y => f i (V a.1, a.2)) q (μ.prod ν) ≤ B := by
    intro i
    rw [← eLpNorm_comp_measurePreserving (hfi i).aestronglyMeasurable he]
    exact hb i
  have hcompact := retained_conditional_responses_isCompact_closure hV hm hn hC hc hpq hqt hB hfi hbi
  let pull := Lp.compMeasurePreserving (E := ℝ) (p := p) e he
  have hiso : Isometry pull := Lp.isometry_compMeasurePreserving he
  have hrep : (fun i =>
      (memLp_condExp_equiv_fst e he hp.out (ne_top_of_lt hpq)
        ((hf i).mono_exponent hpq.le)).toLp
        (P[(fun z => f i (V (e z).1, (e z).2)) |
          (inferInstance : MeasurableSpace A).comap (fun z => (e z).1)])) =
      pull ∘ (fun i =>
        (memLp_condExp_prod_fst hp.out (ne_top_of_lt hpq) ((hfi i).mono_exponent hpq.le)).toLp
          ((μ.prod ν)[(fun a : A × Y => f i (V a.1, a.2)) |
            (inferInstance : MeasurableSpace A).comap Prod.fst])) := by
    funext i
    simpa only [Function.comp_def, e.apply_symm_apply] using
      condExp_equiv_fst_toLp_eq e he (ne_top_of_lt hpq) ((hf i).mono_exponent hpq.le)
  rw [hrep, Set.range_comp pull,
    hiso.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hiso.continuous]
  exact hcompact.image hiso.continuous

end SubdiffusiveProcess
