import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.InteriorSpecialization

/-!
# Per-scale data for the `C^{0,γ}` clause

`HolderHalfAssembly.holder_half_of_per_scale_data` hoists per-`(L,m)` data into
Theorem C's `C^{0,γ}` shape.  This file produces that data at a **finite**
cutoff from the interior anchor, discharging everything except the anchor's own
conclusion.

Note the event: the interior anchor's conclusion holds for **every** `ω`, not
merely almost every `ω`, so the per-scale event is `Set.univ` and the
probability-one requirement is trivial.  The only genuinely probabilistic step is
the transfer of the minimal-scale tail from the model law `M.P` on
`PotentialSample d` to the anchored law on `AnchoredC11Sample d`, which is
`SampleLawBridge`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **Per-scale data at a finite cutoff.**  Hypothesis-shaped on the byte-exact
base clause of `p.cutoff.Holder.regularity.interior` (DRAFT). -/
theorem perScaleData_of_interiorAnchor
    (M : GMCModel d) (C gamma : ℝ) (L m : ℕ)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    (hanchor : ∃ X : PotentialSample d → ℕ,
      Measurable X ∧ (∀ ω, 0 < X ω) ∧
      (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
        (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
          (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
      ∀ ω : PotentialSample d,
        ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
          IsDivFormWeakSolutionOn (aCutoff M L ω) (cube d m) u g →
          MemHolder (cube d m) (1 / 2) g →
          InteriorHolderRegularityConclusions M C L ω gamma m (X ω) u g) :
    ∃ E : Set (AnchoredC11Sample d), MeasurableSet E ∧
      (anchoredC11SampleLaw M hmeas hfull).toMeasure E = 1 ∧
      ∃ Y : AnchoredC11Sample d → ℕ,
        MinimalScaleTail M C gamma hmeas hfull Y ∧
        ∀ ω ∈ E, TheoremCInner M C (L : WithTop ℕ) gamma m Y ω := by
  obtain ⟨X, hXmeas, hXpos, hXtail, hconc⟩ := hanchor
  refine ⟨Set.univ, MeasurableSet.univ, measure_univ,
    liftToAnchored X, ⟨measurable_liftToAnchored hXmeas,
      liftToAnchored_pos hXpos,
      measure_lt_liftToAnchored_le M hmeas hfull hXtail⟩, ?_⟩
  intro ω _
  exact theoremCInner_of_interiorAnchor (X := X) hconc ω

/-- **The `C^{0,γ}` clause at finite cutoffs only.**  Assembles the per-scale
data across all finite `L` and all `m`.  The cutoff `L = ⊤` is *not* covered:
the interior anchor speaks only of finite cutoffs, and the anchored limit is the
separate `S4`-`S6` argument. -/
theorem holder_clause_finite_of_interiorAnchor
    (M : GMCModel d) (C gamma : ℝ)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    (hdata : ∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
      ∃ E : Set (AnchoredC11Sample d), MeasurableSet E ∧
        (anchoredC11SampleLaw M hmeas hfull).toMeasure E = 1 ∧
        ∃ Y : AnchoredC11Sample d → ℕ,
          MinimalScaleTail M C gamma hmeas hfull Y ∧
          ∀ ω ∈ E, TheoremCInner M C L gamma m Y ω) :
    ∃ full : Set (AnchoredC11Sample d),
      MeasurableSet full ∧
      (anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
      ∀ L : WithTop ℕ, ∀ m : ℕ, 0 < m →
        ∃ X : AnchoredC11Sample d → ℕ,
          Measurable X ∧ (∀ ω, 0 < X ω) ∧
          (∀ k : ℕ, 0 < k →
            (anchoredC11SampleLaw M hmeas hfull).toMeasure {ω' | k < X ω'} ≤
              ENNReal.ofReal
                (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ ω ∈ full, TheoremCInner M C L gamma m X ω :=
  holder_half_of_per_scale_data M C gamma hmeas hfull hdata

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
