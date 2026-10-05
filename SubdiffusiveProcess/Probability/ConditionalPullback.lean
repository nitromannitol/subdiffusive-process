module

public import SubdiffusiveProcess.Probability.ProductLpContraction

@[expose] public section

/-! # Conditional expectation under a measure-preserving map

Only measurability in the forward direction is needed. In particular, the
identity from the completed environment to the original product can be used
without claiming that its inverse is measurable. Conditioning is on the
exact pullback sigma-field.
-/

open MeasureTheory Filter Set
open scoped ENNReal MeasureTheory
noncomputable section
namespace SubdiffusiveProcess
variable {X Y : Type*} {m : MeasurableSpace Y}
    [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    {ξ : Measure X} {ζ : Measure Y}

/-- Integrable scalar functions have the same integral after a measure-preserving pullback. -/
theorem integral_comp_of_measurePreserving {g : X → Y}
    (hg : MeasurePreserving g ξ ζ) {f : Y → ℝ} (hf : Integrable f ζ) :
    (∫ x, f (g x) ∂ξ) = ∫ y, f y ∂ζ := by
  have hfm : AEStronglyMeasurable f (ξ.map g) := hg.map_eq.symm ▸ hf.aestronglyMeasurable
  have hi := integral_map hg.aemeasurable hfm
  rw [hg.map_eq] at hi
  exact hi.symm

/-- Conditional expectation pulls back along any measure-preserving map. -/
theorem condExp_comp_measurePreserving [IsFiniteMeasure ξ] [IsFiniteMeasure ζ]
    {g : X → Y} (hg : MeasurePreserving g ξ ζ)
    (hm : m ≤ mY) {f : Y → ℝ} (hf : Integrable f ζ) :
    ξ[f ∘ g | m.comap g] =ᵐ[ξ] (ζ[f | m]) ∘ g := by
  have hle : m.comap g ≤ mX := (MeasurableSpace.comap_mono hm).trans hg.measurable.comap_le
  have hfc := hg.integrable_comp_of_integrable hf
  have hgc := hg.integrable_comp_of_integrable (integrable_condExp (f := f) (m := m))
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle hfc
  · intro s hs hfin
    exact hgc.integrableOn
  · intro s hs hfin
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hgt := hg.restrict_preimage (hm t ht)
    change (∫ x in g ⁻¹' t, (ζ[f | m]) (g x) ∂ξ) = ∫ x in g ⁻¹' t, f (g x) ∂ξ
    rw [integral_comp_of_measurePreserving hgt integrable_condExp.restrict,
      integral_comp_of_measurePreserving hgt hf.restrict]
    exact setIntegral_condExp hm hf ht
  · exact (stronglyMeasurable_condExp.comp_measurable (comap_measurable g)).aestronglyMeasurable

/-- An existing finite conditional moment transfers with the exact conditional expectation. -/
theorem memLp_condExp_pullback [IsFiniteMeasure ξ] [IsFiniteMeasure ζ]
    {g : X → Y} (hg : MeasurePreserving g ξ ζ)
    (hm : m ≤ mY) {f : Y → ℝ} (hf : Integrable f ζ)
    {p : ℝ≥0∞} (hc : MemLp (ζ[f | m]) p ζ) :
    MemLp (ξ[f ∘ g | m.comap g]) p ξ :=
  (hc.comp_measurePreserving hg).ae_eq (condExp_comp_measurePreserving hg hm hf).symm

/-- The pulled-back conditional expectation gives exactly the isometric pullback Lp class. -/
theorem condExp_pullback_toLp_eq [IsFiniteMeasure ξ] [IsFiniteMeasure ζ]
    {g : X → Y} (hg : MeasurePreserving g ξ ζ)
    (hm : m ≤ mY) {f : Y → ℝ} (hf : Integrable f ζ)
    {p : ℝ≥0∞} (hc : MemLp (ζ[f | m]) p ζ) :
    (memLp_condExp_pullback hg hm hf hc).toLp (ξ[f ∘ g | m.comap g]) =
      Lp.compMeasurePreserving g hg (hc.toLp (ζ[f | m])) := by
  apply Lp.ext
  exact ((memLp_condExp_pullback hg hm hf hc).coeFn_toLp.trans
    (condExp_comp_measurePreserving hg hm hf)).trans
      ((Lp.coeFn_compMeasurePreserving _ hg).trans
        (hg.quasiMeasurePreserving.ae_eq_comp hc.coeFn_toLp)).symm

/-- Compact conditional families stay compact on a measure-preserving pullback space. -/
theorem condExp_pullback_isCompact_closure [IsFiniteMeasure ξ] [IsFiniteMeasure ζ]
    {g : X → Y} (hg : MeasurePreserving g ξ ζ)
    (hm : m ≤ mY) {ι : Type*} {f : ι → Y → ℝ}
    (hf : ∀ i, Integrable (f i) ζ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hc : ∀ i, MemLp (ζ[f i | m]) p ζ)
    (hcompact : IsCompact (closure (range (fun i => (hc i).toLp (ζ[f i | m]))))) :
    IsCompact (closure (range (fun i =>
      (memLp_condExp_pullback hg hm (hf i) (hc i)).toLp (ξ[f i ∘ g | m.comap g])))) := by
  let pull := Lp.compMeasurePreserving (E := ℝ) (p := p) g hg
  have hiso : Isometry pull := Lp.isometry_compMeasurePreserving hg
  have hrep : (fun i => (memLp_condExp_pullback hg hm (hf i) (hc i)).toLp
      (ξ[f i ∘ g | m.comap g])) = pull ∘ (fun i => (hc i).toLp (ζ[f i | m])) := by
    funext i
    exact condExp_pullback_toLp_eq hg hm (hf i) (hc i)
  rw [hrep, range_comp pull,
    hiso.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hiso.continuous]
  exact hcompact.image hiso.continuous

end SubdiffusiveProcess
