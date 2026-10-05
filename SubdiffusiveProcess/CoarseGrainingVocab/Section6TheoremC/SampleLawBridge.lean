module

public import SubdiffusiveProcess.Assumptions.AnchoredCoefficient

@[expose] public section

/-!
# Transfer of probabilities between the potential sample and the anchored carrier

Theorem C (`t.large.scale.Holder.multifractal`, `t.large.scale.Holder.multifractal` and `e.limiting.Holder.minimal.scale` and `p.cutoff.Holder.regularity` and `e.cutoff.Holder.minimal.scale`)
states its minimal-scale tail bound `e.limiting.Holder.minimal.scale` under the
anchored sample law `anchoredC11SampleLaw`, while the Hölder regularity
proposition it consumes (`p.cutoff.Holder.regularity`, `t.large.scale.Holder.multifractal` and `e.limiting.Holder.minimal.scale` and `p.cutoff.Holder.regularity` and `e.cutoff.Holder.minimal.scale`)
states the corresponding bound `e.cutoff.Holder.minimal.scale` under the model
law `M.P` on `PotentialSample d`.

Since `anchoredC11SampleLaw` is the comap of `M.P` along the inclusion of a
full-measure subtype, the two agree on every preimage.  This file records that
transfer, together with the measurability of a lifted random variable, so that
the tail bound supplied by the regularity anchor can be quoted verbatim on the
anchored carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory _root_.SubdiffusiveProcess.Model
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The inclusion of the anchored carrier into the potential samples is a
measurable embedding once the good event is measurable. -/
theorem measurableEmbedding_anchoredVal
    (hmeas : MeasurableSet (anchoredC11GoodSet d)) :
    MeasurableEmbedding (Subtype.val : AnchoredC11Sample d → PotentialSample d) :=
  MeasurableEmbedding.subtype_coe hmeas

/-- The image of a preimage under the anchored inclusion is the intersection
with the good event. -/
theorem image_preimage_anchoredVal (S : Set (PotentialSample d)) :
    (Subtype.val : AnchoredC11Sample d → PotentialSample d) ''
        (Subtype.val ⁻¹' S) =
      S ∩ anchoredC11GoodSet d := by
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
  rfl

/-- The anchored sample law of a preimage is the model probability of the
underlying event. -/
theorem anchoredC11SampleLaw_preimage (M : GMCModel d)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    (S : Set (PotentialSample d)) :
    (anchoredC11SampleLaw M hmeas hfull).toMeasure (Subtype.val ⁻¹' S) =
      M.P.toMeasure S := by
  have hcomap :
      (anchoredC11SampleLaw M hmeas hfull).toMeasure
          (Subtype.val ⁻¹' S) =
        M.P.toMeasure
          ((Subtype.val : AnchoredC11Sample d → PotentialSample d) ''
            (Subtype.val ⁻¹' S)) :=
    (measurableEmbedding_anchoredVal hmeas).comap_apply
      (μ := M.P.toMeasure) _
  rw [hcomap, image_preimage_anchoredVal]
  -- The good event is full, so intersecting with it does not change the measure.
  have hcompl : M.P.toMeasure (anchoredC11GoodSet d)ᶜ = 0 := by
    rw [measure_compl hmeas (measure_ne_top _ _), hfull,
      measure_univ, tsub_self]
  exact measure_inter_conull hcompl

/-! ### Transfer of a minimal scale and its tail bound

Theorem C's minimal scale `𝓛_L(γ,m)` is an `ℕ`-valued random variable on the
anchored carrier satisfying `e.limiting.Holder.minimal.scale`
(`e.limiting.Holder.minimal.scale` and `p.cutoff.Holder.regularity` and `e.cutoff.Holder.minimal.scale`), while `p.cutoff.Holder.regularity` produces its
minimal scale `𝓛_L(α,m)` on `PotentialSample d` with the identical tail
`e.cutoff.Holder.minimal.scale` (`e.limiting.Holder.minimal.scale` and `p.cutoff.Holder.regularity` and `e.cutoff.Holder.minimal.scale`).  Composing with
the inclusion transports the one to the other, bound unchanged. -/

/-- A random variable on the potential samples, restricted to the anchored
carrier. -/
def liftToAnchored (X : PotentialSample d → ℕ) :
    AnchoredC11Sample d → ℕ :=
  fun ω ↦ X ω.1

@[simp]
theorem liftToAnchored_apply (X : PotentialSample d → ℕ)
    (ω : AnchoredC11Sample d) : liftToAnchored X ω = X ω.1 :=
  rfl

/-- The lifted variable is measurable. -/
theorem measurable_liftToAnchored {X : PotentialSample d → ℕ}
    (hX : Measurable X) : Measurable (liftToAnchored X) :=
  hX.comp measurable_subtype_coe

/-- The lifted variable is positive wherever the original is. -/
theorem liftToAnchored_pos {X : PotentialSample d → ℕ}
    (hX : ∀ ω, 0 < X ω) (ω : AnchoredC11Sample d) :
    0 < liftToAnchored X ω :=
  hX ω.1

/-- The upper-excursion event of the lifted variable is the preimage of that of
the original. -/
theorem setOf_lt_liftToAnchored (X : PotentialSample d → ℕ) (k : ℕ) :
    {ω : AnchoredC11Sample d | k < liftToAnchored X ω} =
      Subtype.val ⁻¹' {ω : PotentialSample d | k < X ω} :=
  rfl

/-- **Tail transfer.**  A minimal scale on `PotentialSample d` obeying a tail
bound under the model law lifts to the anchored carrier with the *same* bound
under the anchored sample law.  This carries
`e.cutoff.Holder.minimal.scale` to `e.limiting.Holder.minimal.scale`. -/
theorem measure_lt_liftToAnchored_le (M : GMCModel d)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    {X : PotentialSample d → ℕ} {B : ℕ → ℝ≥0∞}
    (hX : ∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ B k)
    (k : ℕ) (hk : 0 < k) :
    (anchoredC11SampleLaw M hmeas hfull).toMeasure
        {ω | k < liftToAnchored X ω} ≤ B k := by
  rw [setOf_lt_liftToAnchored, anchoredC11SampleLaw_preimage]
  exact hX k hk

/-- The packaged form: the lifted minimal scale is measurable, positive, and
inherits the tail bound. -/
theorem exists_liftToAnchored_of_minimalScale (M : GMCModel d)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    {X : PotentialSample d → ℕ} {B : ℕ → ℝ≥0∞}
    (hmeasX : Measurable X) (hpos : ∀ ω, 0 < X ω)
    (hX : ∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ B k) :
    ∃ Y : AnchoredC11Sample d → ℕ,
      Measurable Y ∧ (∀ ω, 0 < Y ω) ∧
        (∀ k : ℕ, 0 < k →
          (anchoredC11SampleLaw M hmeas hfull).toMeasure {ω | k < Y ω} ≤ B k) ∧
        ∀ ω, Y ω = X ω.1 :=
  ⟨liftToAnchored X, measurable_liftToAnchored hmeasX,
    liftToAnchored_pos hpos,
    measure_lt_liftToAnchored_le M hmeas hfull hX, fun _ ↦ rfl⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
