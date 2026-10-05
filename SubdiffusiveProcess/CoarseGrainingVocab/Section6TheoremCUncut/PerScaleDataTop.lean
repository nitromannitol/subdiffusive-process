module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.TopDisplays
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.PerScaleData
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open _root_.SubdiffusiveProcess.Model

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### A measurable full event carrying an almost-sure property -/

/-- An almost-sure property holds on a measurable event of probability one. -/
theorem exists_measurable_full_of_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → Prop}
    (h : ∀ᵐ ω ∂μ, p ω) :
    ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧ ∀ ω ∈ E, p ω := by
  classical
  refine ⟨(toMeasurable μ {ω | ¬ p ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [prob_compl_eq_one_iff (measurableSet_toMeasurable _ _),
      measure_toMeasurable]
    exact ae_iff.1 h
  · intro ω hω
    by_contra hp
    exact hω (subset_toMeasurable μ {ω | ¬ p ω} hp)

/-! ### The per-scale package at `L = ⊤`, from the convergence package -/

/-- **The uncut per-scale package, from the anchored convergence package.**
The growth envelope and the compact uniform convergence are exactly the two
conjuncts of `l.finite.cutoff.coefficient.convergence` that the limit needs. -/
theorem perScaleDataTop_of_convergence
    (M : GMCModel d) (C gamma : ℝ)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    {kappa : ℝ} (hkappa : 0 ≤ kappa)
    {Comega : AnchoredC11Sample d → ℝ}
    (hae : ∀ᵐ omega ∂(anchoredC11SampleLaw M hmeas hfull).toMeasure,
      0 ≤ Comega omega ∧
      (∀ x : Vec d,
        aAnchored M omega x + (aAnchored M omega x)⁻¹ +
              euclideanNorm (aAnchored M omega x •
                shellGradient (anchoredLog omega) x) ≤
            Comega omega * (1 + ‖x‖) ^ kappa ∧
          ∀ L : ℕ,
            anchoredCutoff M L omega.1 x + (anchoredCutoff M L omega.1 x)⁻¹ +
                euclideanNorm (anchoredCutoff M L omega.1 x •
                  shellGradient (anchoredPartialSumField omega.1 L) x) ≤
              Comega omega * (1 + ‖x‖) ^ kappa) ∧
      ∀ K : Set (Vec d), IsCompact K →
        TendstoUniformlyOn (fun L x ↦ anchoredCutoff M L omega.1 x)
          (aAnchored M omega) atTop K)
    (hanchor : ∀ L m : ℕ,
      (m ≤ L → ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
        Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
        (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
          (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
            (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
        ∀ J : ℕ, m ≤ J → ∀ ω,
          ∀ (u : H1Function (openCubeSet (originCube d m)))
              (g : Vec d → Vec d),
            IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
                (cube d m) u g →
            MemHolder (cube d m) (1 / 2) g →
            InteriorHolderRegularityConclusions M C J ω gamma m (Xuncut ω) u g)) :
    ∀ m : ℕ, 0 < m →
      ∃ E : Set (AnchoredC11Sample d), MeasurableSet E ∧
        (anchoredC11SampleLaw M hmeas hfull).toMeasure E = 1 ∧
        ∃ Y : AnchoredC11Sample d → ℕ,
          MinimalScaleTail M C gamma hmeas hfull Y ∧
          ∀ ω ∈ E, TheoremCInner M C (⊤ : WithTop ℕ) gamma m Y ω := by
  classical
  have : NeZero d := ⟨by have hd := M.shellPrefix.dimension; omega⟩
  intro m _
  obtain ⟨E, hEmeas, hEfull, hEprop⟩ :=
    exists_measurable_full_of_ae _ hae
  obtain ⟨Xuncut, hXmeas, hXpos, hXtail, hXconc⟩ := hanchor m m le_rfl
  refine ⟨E, hEmeas, hEfull, liftToAnchored Xuncut,
    ⟨measurable_liftToAnchored hXmeas, liftToAnchored_pos hXpos,
      measure_lt_liftToAnchored_le M hmeas hfull hXtail⟩, ?_⟩
  intro ω hω u hu
  obtain ⟨hCnn, henv, hcompact⟩ := hEprop ω hω
  obtain ⟨lam, Lam, hlam, hbA, hbC⟩ :=
    exists_uniform_bounds_cube M ω (m : ℤ) hkappa hCnn
      (fun x ↦ (henv x).1) (fun x L ↦ (henv x).2 L)
  exact theoremCDisplays_top_of_uncutAnchor hlam hbA hbC
    ((hcompact (closure (cube d (m : ℤ))) (isCompact_closure_cube d (m : ℤ))))
    (fun J hJ p g hdiv hg ↦ hXconc J hJ ω.1 p g hdiv hg) u hu

/-! ### The endpoint: the `L = ⊤` instance of Theorem C's `hdata` -/



theorem perScaleDataTop_of_interiorUncutAnchor (d : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
        ∀ C gamma : ℝ,
          (∀ L m : ℕ,
            (m ≤ L → ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤
                ENNReal.ofReal
                (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDivFormWeakSolutionOn
                      (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
                      (cube d m) u g →
                  MemHolder (cube d m) (1 / 2) g →
                  InteriorHolderRegularityConclusions M C J ω gamma m
                    (Xuncut ω) u g)) →
          ∀ m : ℕ, 0 < m →
            ∃ E : Set (AnchoredC11Sample d), MeasurableSet E ∧
              (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
                (measure_anchoredC11GoodSet_eq_one M)).toMeasure E = 1 ∧
              ∃ Y : AnchoredC11Sample d → ℕ,
                MinimalScaleTail M C gamma
                  (measurableSet_anchoredC11GoodSet d)
                  (measure_anchoredC11GoodSet_eq_one M) Y ∧
                ∀ ω ∈ E, TheoremCInner M C (⊤ : WithTop ℕ) gamma m Y ω := by
  classical
  obtain ⟨delta0, hdelta0, hconv⟩ :=
    SubdiffusiveProcess.Frozen.Section6.finite_cutoff_coefficient_convergence d
  refine ⟨delta0, hdelta0, fun M hM C gamma hanchor ↦ ?_⟩
  obtain ⟨_hmeas', _hfull', kappa, hkappa, Comega, _hCmeas, hae⟩ := hconv M hM
  refine perScaleDataTop_of_convergence M C gamma
    (measurableSet_anchoredC11GoodSet d) (measure_anchoredC11GoodSet_eq_one M)
    (kappa := kappa) hkappa.1.le (Comega := Comega) ?_ hanchor
  filter_upwards [hae] with omega homega
  exact ⟨homega.1, homega.2.1, fun K hK ↦ (homega.2.2.1 K hK).1⟩

/-! ### Both branches together: the whole `hdata` premise -/

/-- **Theorem C's `hdata`, at every cutoff.**  The finite branch is
`Section6TheoremC.perScaleData_of_interiorAnchor` applied to the frozen
anchor's base clause; the `L = ⊤` branch is
`perScaleDataTop_of_interiorUncutAnchor` applied to its uncut clause.  Together
they discharge the `hdata` premise of
`SubdiffusiveProcess.Providers.Section6.large_scale_holder_multifractal_of_halves` for a single
model, given only those two frozen clauses. -/
theorem perScaleData_all_of_interiorAnchor (d : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
        ∀ C gamma : ℝ,
          (∀ L m : ℕ,
            (∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable X ∧ (∀ ω, 0 < X ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C L ω gamma m (X ω) u g)) →
          (∀ L m : ℕ,
            (m ≤ L → ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤
                ENNReal.ofReal
                (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDivFormWeakSolutionOn
                      (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
                      (cube d m) u g →
                  MemHolder (cube d m) (1 / 2) g →
                  InteriorHolderRegularityConclusions M C J ω gamma m
                    (Xuncut ω) u g)) →
          ∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
            ∃ E : Set (AnchoredC11Sample d), MeasurableSet E ∧
              (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
                (measure_anchoredC11GoodSet_eq_one M)).toMeasure E = 1 ∧
              ∃ Y : AnchoredC11Sample d → ℕ,
                MinimalScaleTail M C gamma
                  (measurableSet_anchoredC11GoodSet d)
                  (measure_anchoredC11GoodSet_eq_one M) Y ∧
                ∀ ω ∈ E, TheoremCInner M C L gamma m Y ω := by
  classical
  obtain ⟨delta0, hdelta0, htop⟩ := perScaleDataTop_of_interiorUncutAnchor d
  refine ⟨delta0, hdelta0, fun M hM C gamma hbase huncut L m hm ↦ ?_⟩
  induction L using WithTop.recTopCoe with
  | top => exact htop M hM C gamma huncut m hm
  | coe n =>
      exact perScaleData_of_interiorAnchor M C gamma n m
        (measurableSet_anchoredC11GoodSet d)
        (measure_anchoredC11GoodSet_eq_one M) (hbase n m)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
