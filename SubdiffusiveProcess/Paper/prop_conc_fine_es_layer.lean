module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-! Efron--Stein for one fixed base, transferred to the layer variable: if the pieces `T y` of a layer sample
`y ~ μ` have the product law `⊗ μk`, then the `L^p(μ)` fluctuation of `Ψ ∘ T` about `∫Ψ d(⊗ μk)` is
controlled by the conditional variance proxy along `T y`.  The Efron--Stein inequality itself is an
argument `hES` (the moment form of the standard inequality, supplied by `SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality`
in the consumer). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

theorem prop_conc_fine_es_layer {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {m : ℕ} (μk : Fin m → Measure X) [∀ k, IsProbabilityMeasure (μk k)]
    (T : X → (Fin m → X)) (hT : Measurable T) (hπ : μ.map T = Measure.pi μk)
    (Ψ : (Fin m → X) → ℝ) (hΨ : Measurable Ψ) (p Cp : ℝ)
    (hES : ∀ F : (Fin m → X) → ℝ, AEStronglyMeasurable F (Measure.pi μk) →
      MemLp F (ENNReal.ofReal p) (Measure.pi μk) →
      eLpNorm (fun x => F x - ∫ y, F y ∂(Measure.pi μk)) (ENNReal.ofReal p) (Measure.pi μk) ≤
        ENNReal.ofReal Cp *
          eLpNorm (fun x => Real.sqrt
            (∑ i : Fin m, ∫ y : X, (F x - F (Function.update x i y)) ^ 2 ∂μk i))
            (ENNReal.ofReal p) (Measure.pi μk))
    (hmem : MemLp Ψ (ENNReal.ofReal p) (Measure.pi μk)) :
    eLpNorm (fun y => Ψ (T y) - ∫ v, Ψ v ∂(Measure.pi μk)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal Cp *
        eLpNorm (fun y => Real.sqrt (∑ i : Fin m, ∫ z : X,
          (Ψ (T y) - Ψ (Function.update (T y) i z)) ^ 2 ∂μk i)) (ENNReal.ofReal p) μ := by
  have h := hES Ψ hΨ.aestronglyMeasurable hmem
  have hVin : ∀ i : Fin m, Measurable (fun q : (Fin m → X) × X =>
      (Ψ q.1 - Ψ (Function.update q.1 i q.2)) ^ 2) := by
    intro i
    have h1 : Measurable (fun q : (Fin m → X) × X => Ψ q.1) := hΨ.comp measurable_fst
    have h2 : Measurable (fun q : (Fin m → X) × X => Ψ (Function.update q.1 i q.2)) :=
      hΨ.comp (measurable_update'.comp (measurable_fst.prodMk measurable_snd))
    exact (h1.sub h2).pow_const 2
  have hV : Measurable (fun x : Fin m → X => Real.sqrt (∑ i : Fin m, ∫ y : X,
      (Ψ x - Ψ (Function.update x i y)) ^ 2 ∂μk i)) := by
    refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => ?_)
    exact ((hVin i).stronglyMeasurable.integral_prod_right' (ν := μk i)).measurable
  have hc : Measurable (fun x : Fin m → X => Ψ x - ∫ v, Ψ v ∂(Measure.pi μk)) :=
    hΨ.sub measurable_const
  have e1 := eLpNorm_map_measure (μ := μ) (f := T) (p := ENNReal.ofReal p)
    (g := fun x : Fin m → X => Ψ x - ∫ v, Ψ v ∂(Measure.pi μk))
    (by rw [hπ]; exact hc.aestronglyMeasurable) hT.aemeasurable
  have e2 := eLpNorm_map_measure (μ := μ) (f := T) (p := ENNReal.ofReal p)
    (g := fun x : Fin m → X => Real.sqrt (∑ i : Fin m, ∫ y : X,
      (Ψ x - Ψ (Function.update x i y)) ^ 2 ∂μk i))
    (by rw [hπ]; exact hV.aestronglyMeasurable) hT.aemeasurable
  rw [hπ] at e1 e2
  rw [e1, e2] at h
  exact h

end
end SubdiffusiveProcess.Paper
