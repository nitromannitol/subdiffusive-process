module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.OuterStructure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SampleLawBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.FiniteCutoffConclusion

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The pair of displays of Theorem C at one sample, cutoff, scale and
solution: `e.large.scale.Holder.multifractal` and
`e.large.scale.energy.multifractal`, written exactly as the statement
writes them. -/
def TheoremCDisplays (M : GMCModel d) (C : ℝ) (L : WithTop ℕ) (gamma : ℝ)
    (m X : ℕ) (ω : AnchoredC11Sample d)
    (u : H1Function (openCubeSet (originCube d m))) : Prop :=
  ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) →
    ∀ z : Vec d, OnTriadicGrid n z →
      translatedCube d n z ⊆ cube d ((m : ℤ) - 1) →
        normalizedL2On (translatedCube d (n : ℤ) z)
            (fun x ↦ u.toFun x -
              averageOn (translatedCube d (n : ℤ) z) u.toFun) ≤
          C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
            normalizedL2On (cube d m)
              (fun x ↦ u.toFun x - averageOn (cube d m) u.toFun) ∧
        vectorNormalizedL2On (translatedCube d (n : ℤ) z)
            (fun x ↦ Real.sqrt (coefficientAt M L ω x) • u.grad x) ≤
          C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
            vectorNormalizedL2On (cube d m)
              (fun x ↦ Real.sqrt (coefficientAt M L ω x) • u.grad x)

/-- The per-sample conclusion of Theorem C's `C^{0,γ}` clause. -/
def TheoremCInner (M : GMCModel d) (C : ℝ) (L : WithTop ℕ) (gamma : ℝ)
    (m : ℕ) (X : AnchoredC11Sample d → ℕ) (ω : AnchoredC11Sample d) : Prop :=
  ∀ u : H1Function (openCubeSet (originCube d m)),
    IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) u →
    TheoremCDisplays M C L gamma m (X ω) ω u

/-- The minimal-scale tail bound of `e.limiting.Holder.minimal.scale`. -/
def MinimalScaleTail (M : GMCModel d) (C gamma : ℝ)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    (X : AnchoredC11Sample d → ℕ) : Prop :=
  Measurable X ∧ (∀ ω, 0 < X ω) ∧
    ∀ k : ℕ, 0 < k →
      (anchoredC11SampleLaw M hmeas hfull).toMeasure {ω' | k < X ω'} ≤
        ENNReal.ofReal
          (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
            (C * M.delta ^ 2 * |Real.log M.delta|)))

/-- **The `C^{0,γ}` half, assembled.**  Per-`(L,m)` data, each on its own
probability-one event, hoists into the shape: a *single* event serving
every cutoff and scale, with the minimal-scale witness depending on both.

The conclusion is the statement's `C^{0,γ}` clause verbatim, so the
provider applies this as a term. -/
theorem holder_half_of_per_scale_data (M : GMCModel d) (C gamma : ℝ)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    (hdata : ∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
      ∃ E : Set (AnchoredC11Sample d), MeasurableSet E ∧
        (anchoredC11SampleLaw M hmeas hfull).toMeasure E = 1 ∧
        ∃ X : AnchoredC11Sample d → ℕ,
          MinimalScaleTail M C gamma hmeas hfull X ∧
          ∀ ω ∈ E, TheoremCInner M C L gamma m X ω) :
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
          ∀ ω ∈ full, TheoremCInner M C L gamma m X ω := by
  classical
  obtain ⟨full, hfm, hf1, hall⟩ :=
    exists_full_forall_cutoff_scale_pos
      (A := AnchoredC11Sample d → ℕ)
      (anchoredC11SampleLaw M hmeas hfull).toMeasure
      (S := fun L m X ↦ MinimalScaleTail M C gamma hmeas hfull X)
      (R := fun L m X ω ↦ TheoremCInner M C L gamma m X ω)
      hdata (fun _ ↦ 1)
  refine ⟨full, hfm, hf1, fun L m hm ↦ ?_⟩
  obtain ⟨X, hS, hR⟩ := hall L m hm
  exact ⟨X, hS.1, hS.2.1, hS.2.2, hR⟩

/-- **The loop closed at a finite cutoff.**  The conclusion package
delivers `TheoremCDisplays` directly, so the `C^{0,γ}` half reduces to the *supply* of
that package -- which is the interior variant. -/
theorem theoremCDisplays_of_holderRegularityConclusions
    {M : GMCModel d} {C : ℝ} {L m X : ℕ} {gamma : ℝ}
    {ω : AnchoredC11Sample d}
    {u : H1Function (openCubeSet (originCube d m))}
    (hconc : HolderRegularityConclusions M C L ω.1 gamma m X u u
      (fun _ ↦ (0 : Vec d))) :
    TheoremCDisplays M C (L : WithTop ℕ) gamma m X ω u :=
  finite_cutoff_holder_displays hconc

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
