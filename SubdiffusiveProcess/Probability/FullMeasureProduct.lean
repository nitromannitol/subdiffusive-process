module

public import SubdiffusiveProcess.Probability.LayerProductBlocks

@[expose] public section

/-! # Keeping the product law on a full-measure tail carrier

If a good environment condition depends only on the discarded block, the
good environments are measurably equivalent to the retained block times the
good discarded block. This is an actual restriction of the original law.
-/

open MeasureTheory Filter Set
open scoped ENNReal MeasureTheory
noncomputable section
namespace SubdiffusiveProcess
variable {Z A Y : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace Y]

/-- Restrict a product decomposition to a condition on its second coordinate. -/
def fullMeasureProductEquiv (e : Z ≃ᵐ A × Y) (s : Set Z) (t : Set Y)
    (h : ∀ z, z ∈ s ↔ (e z).2 ∈ t) : s ≃ᵐ A × t where
  toFun z := ((e z.val).1, ⟨(e z.val).2, (h z.val).mp z.property⟩)
  invFun z := ⟨e.symm (z.1, z.2.val), (h _).mpr (by simpa only [e.apply_symm_apply] using z.2.property)⟩
  left_inv z := by
    apply Subtype.ext
    exact e.symm_apply_apply z.val
  right_inv z := by
    dsimp only
    simp only [e.apply_symm_apply]
  measurable_toFun := (measurable_fst.comp (e.measurable.comp measurable_subtype_coe)).prodMk
    ((measurable_snd.comp (e.measurable.comp measurable_subtype_coe)).subtype_mk)
  measurable_invFun := (e.symm.measurable.comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))).subtype_mk

/-- The full-measure subtype inclusion preserves its original measure. -/
theorem measurePreserving_fullMeasure_subtype {P : Measure Z} {s : Set Z}
    (hs : MeasurableSet s) (hfull : ∀ᵐ z ∂P, z ∈ s) :
    MeasurePreserving (Subtype.val : s → Z) (P.comap Subtype.val) P :=
  ⟨measurable_subtype_coe, (map_comap_subtype_coe hs P).trans (Measure.restrict_eq_self_of_ae_mem hfull)⟩

/-- A full-measure condition depending on the discarded block has full discarded probability. -/
theorem ae_discarded_of_ae_product_condition {P : Measure Z} {μ : Measure A} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : Z ≃ᵐ A × Y) (he : MeasurePreserving e P (μ.prod ν))
    {s : Set Z} {t : Set Y} (ht : MeasurableSet t)
    (h : ∀ z, z ∈ s ↔ (e z).2 ∈ t) (hfull : ∀ᵐ z ∂P, z ∈ s) :
    ∀ᵐ y ∂ν, y ∈ t := by
  have hp := (measurePreserving_snd (μ := μ) (ν := ν)).comp he
  rw [← hp.map_eq]
  exact (ae_map_iff hp.aemeasurable ht).mpr (hfull.mono (fun z hz => (h z).mp hz))

/-- The restricted decomposition has the original retained law and the full-probability tail law. -/
theorem measurePreserving_fullMeasureProductEquiv {P : Measure Z} {μ : Measure A} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : Z ≃ᵐ A × Y) (he : MeasurePreserving e P (μ.prod ν))
    {s : Set Z} {t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : ∀ z, z ∈ s ↔ (e z).2 ∈ t) (hfull : ∀ᵐ z ∂P, z ∈ s) :
    MeasurePreserving (fullMeasureProductEquiv e s t h) (P.comap Subtype.val)
      (μ.prod (ν.comap Subtype.val)) := by
  let E := fullMeasureProductEquiv e s t h
  let i : A × t → A × Y := fun z => (z.1, z.2.val)
  have hi : MeasurableEmbedding i := (MeasurableEmbedding.id).prodMap (MeasurableEmbedding.subtype_coe ht)
  have hiP : MeasurePreserving i (μ.prod (ν.comap Subtype.val)) (μ.prod ν) :=
    (MeasurePreserving.id μ).prod (measurePreserving_fullMeasure_subtype ht
      (ae_discarded_of_ae_product_condition e he ht h hfull))
  have hcomp : MeasurePreserving (i ∘ E) (P.comap Subtype.val) (μ.prod ν) :=
    he.comp (measurePreserving_fullMeasure_subtype hs hfull)
  refine ⟨E.measurable, ?_⟩
  have heq : ((P.comap Subtype.val).map E).map i = (μ.prod (ν.comap Subtype.val)).map i := by
    rw [Measure.map_map hi.measurable E.measurable, hcomp.map_eq, hiP.map_eq]
  have hc := congrArg (Measure.comap i) heq
  simpa only [hi.comap_map] using hc

end SubdiffusiveProcess
