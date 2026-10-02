import SubdiffusiveProcess.Probability.FullMeasureProduct
import SubdiffusiveProcess.Probability.ConditionalPullback

/-! # Scalar representatives on the original environment

A response defined on a measurable full-measure carrier is extended by zero
on its null complement. This chooses only a scalar representative, not a
random field or an off-support conditional value. All norm and conditional
identities are independent of the values on that complement.
-/

open MeasureTheory Filter Set
open scoped ENNReal MeasureTheory
noncomputable section
namespace SubdiffusiveProcess
variable {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    {μ : Measure X} {s : Set X}

/-- Extend a scalar function from its carrier by zero. -/
def scalarZeroExtension (s : Set X) (f : s → ℝ) (x : X) : ℝ := by
  classical
  exact if h : x ∈ s then f ⟨x, h⟩ else 0

omit mX in
/-- Restriction of the chosen representative is exactly the original response. -/
theorem scalarZeroExtension_subtype (f : s → ℝ) (x : s) :
    scalarZeroExtension s f x.val = f x := by
  simp only [scalarZeroExtension, dif_pos x.property]

/-- The scalar extension is measurable whenever the original response is measurable. -/
theorem measurable_scalarZeroExtension (hs : MeasurableSet s) {f : s → ℝ} (hf : Measurable f) :
    Measurable (scalarZeroExtension s f) := by
  classical
  exact hf.dite measurable_const hs

/-- Scalar extensions have exactly the original moments on a full-measure carrier. -/
theorem memLp_scalarZeroExtension_iff (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s)
    {f : s → ℝ} {p : ℝ≥0∞} :
    MemLp (scalarZeroExtension s f) p μ ↔ MemLp f p (μ.comap Subtype.val) := by
  have he := measurePreserving_fullMeasure_subtype hs hfull
  have h := (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff
    (g := scalarZeroExtension s f) (p := p) (μ := μ.comap Subtype.val)
  rw [he.map_eq] at h
  simpa only [Function.comp_def, scalarZeroExtension_subtype] using h

/-- The extension does not change any eLp norm. -/
theorem eLpNorm_scalarZeroExtension (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s)
    (f : s → ℝ) (p : ℝ≥0∞) :
    eLpNorm (scalarZeroExtension s f) p μ = eLpNorm f p (μ.comap Subtype.val) := by
  have he := measurePreserving_fullMeasure_subtype hs hfull
  have h := (MeasurableEmbedding.subtype_coe hs).eLpNorm_map_measure
    (g := scalarZeroExtension s f) (p := p) (μ := μ.comap Subtype.val)
  rw [he.map_eq] at h
  simpa only [Function.comp_def, scalarZeroExtension_subtype] using h

/-- Any other scalar representative agreeing on the carrier is almost everywhere equal. -/
theorem scalarZeroExtension_ae_eq (hfull : ∀ᵐ x ∂μ, x ∈ s) (f : s → ℝ)
    {g : X → ℝ} (hg : ∀ x : s, g x.val = f x) :
    scalarZeroExtension s f =ᵐ[μ] g := by
  filter_upwards [hfull] with x hx
  exact (scalarZeroExtension_subtype f ⟨x, hx⟩).trans (hg ⟨x, hx⟩).symm

/-- Conditional expectation of the ambient representative restricts to the actual carrier conditional expectation. -/
theorem condExp_scalarZeroExtension_subtype [IsFiniteMeasure μ]
    (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) (hm : m ≤ mX)
    {f : s → ℝ} (hf : Integrable f (μ.comap Subtype.val)) :
    (μ.comap Subtype.val)[f | m.comap (Subtype.val : s → X)] =ᵐ[μ.comap Subtype.val]
      (μ[scalarZeroExtension s f | m]) ∘ Subtype.val := by
  have he := measurePreserving_fullMeasure_subtype hs hfull
  have hfe : Integrable (scalarZeroExtension s f) μ :=
    memLp_one_iff_integrable.mp ((memLp_scalarZeroExtension_iff hs hfull).mpr (memLp_one_iff_integrable.mpr hf))
  simpa only [Function.comp_def, scalarZeroExtension_subtype] using
    condExp_comp_measurePreserving he hm hfe

/-- Any carrier formula for the conditional expectation gives the ambient formula almost everywhere. -/
theorem condExp_scalarZeroExtension_ae_formula [IsFiniteMeasure μ]
    (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) (hm : m ≤ mX)
    {f : s → ℝ} (hf : Integrable f (μ.comap Subtype.val)) {g : X → ℝ}
    (hformula : (μ.comap Subtype.val)[f | m.comap (Subtype.val : s → X)] =ᵐ[μ.comap Subtype.val]
      g ∘ Subtype.val) :
    μ[scalarZeroExtension s f | m] =ᵐ[μ] g := by
  have he := measurePreserving_fullMeasure_subtype hs hfull
  have h := (condExp_scalarZeroExtension_subtype hs hfull hm hf).symm.trans hformula
  have h' : ∀ᵐ x ∂(μ.comap Subtype.val).map (Subtype.val : s → X),
      (μ[scalarZeroExtension s f | m]) x = g x :=
    (MeasurableEmbedding.subtype_coe hs).ae_map_iff.mpr h
  simpa only [he.map_eq] using h'

/-- The ambient conditional moment follows from the proved carrier moment. -/
theorem memLp_condExp_scalarZeroExtension [IsFiniteMeasure μ]
    (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) (hm : m ≤ mX)
    {f : s → ℝ} (hf : Integrable f (μ.comap Subtype.val)) {p : ℝ≥0∞}
    (hc : MemLp ((μ.comap Subtype.val)[f | m.comap (Subtype.val : s → X)]) p
      (μ.comap Subtype.val)) :
    MemLp (μ[scalarZeroExtension s f | m]) p μ := by
  have he := measurePreserving_fullMeasure_subtype hs hfull
  have h := (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff
    (g := μ[scalarZeroExtension s f | m]) (p := p) (μ := μ.comap Subtype.val)
  rw [he.map_eq] at h
  exact h.mpr (hc.ae_eq (condExp_scalarZeroExtension_subtype hs hfull hm hf))

/-- Conditional compactness on a full-measure carrier implies ambient conditional compactness. -/
theorem condExp_scalarZeroExtension_isCompact_closure [IsFiniteMeasure μ]
    (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) (hm : m ≤ mX)
    {ι : Type*} {f : ι → s → ℝ} (hf : ∀ i, Integrable (f i) (μ.comap Subtype.val))
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hc : ∀ i, MemLp ((μ.comap Subtype.val)[f i | m.comap (Subtype.val : s → X)]) p
      (μ.comap Subtype.val))
    (hcompact : IsCompact (closure (range (fun i => (hc i).toLp
      ((μ.comap Subtype.val)[f i | m.comap (Subtype.val : s → X)]))))) :
    IsCompact (closure (range (fun i =>
      (memLp_condExp_scalarZeroExtension hs hfull hm (hf i) (hc i)).toLp
        (μ[scalarZeroExtension s (f i) | m])))) := by
  have he := measurePreserving_fullMeasure_subtype hs hfull
  let pull := Lp.compMeasurePreserving (E := ℝ) (p := p) Subtype.val he
  have hiso : Isometry pull := Lp.isometry_compMeasurePreserving he
  have hrep : (fun i => (hc i).toLp
      ((μ.comap Subtype.val)[f i | m.comap (Subtype.val : s → X)])) =
      pull ∘ (fun i => (memLp_condExp_scalarZeroExtension hs hfull hm (hf i) (hc i)).toLp
        (μ[scalarZeroExtension s (f i) | m])) := by
    funext i
    apply Lp.ext
    exact ((hc i).coeFn_toLp.trans (condExp_scalarZeroExtension_subtype hs hfull hm (hf i))).trans
      ((Lp.coeFn_compMeasurePreserving _ he).trans
        (he.quasiMeasurePreserving.ae_eq
          (memLp_condExp_scalarZeroExtension hs hfull hm (hf i) (hc i)).coeFn_toLp)).symm
  apply hiso.isEmbedding.isCompact_iff.mpr
  rw [hrep, range_comp pull,
    hiso.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hiso.continuous] at hcompact
  exact hcompact

end SubdiffusiveProcess
