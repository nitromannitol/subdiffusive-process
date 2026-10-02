import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.LiouvilleInputs
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.MinimalScaleSummability
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CountableFullEvents




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Positivity of the tail-bound constants -/

/-- The denominator of the minimal-scale tail is positive. -/
theorem tail_denominator_pos (M : GMCModel d) {C : ℝ} (hC : 0 < C) :
    0 < C * M.delta ^ 2 * |Real.log M.delta| := by
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hdhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hlogneg : Real.log M.delta < 0 := Real.log_neg hdpos (by linarith)
  have habs : 0 < |Real.log M.delta| := abs_pos.2 (ne_of_lt hlogneg)
  positivity

/-! ### S7: Borel–Cantelli along the shifted diagonal -/

/-- **S7.**  For a fixed inner scale `n`, the minimal scale of every large
outer scale `m` is below `m − n`, almost surely.

`Y j` plays the role of `𝓛_L(γ_reg, n + j + 1)`: the shift by `n + 1` keeps the
tail index `j + 1` strictly positive, which is where the frozen bound lives. -/
theorem ae_eventually_minimalScale_le (M : GMCModel d)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    {C gamma : ℝ} (hC : 0 < C) (hgamma : gamma < 1)
    {Y : ℕ → AnchoredC11Sample d → ℕ}
    (hYtail : ∀ j : ℕ,
      (anchoredC11SampleLaw M hmeas hfull).toMeasure {ω' | j + 1 < Y j ω'} ≤
        ENNReal.ofReal
          (C * Real.exp (-((1 - gamma) ^ 2 * max (((j + 1 : ℕ) : ℝ) - C) 0) /
            (C * M.delta ^ 2 * |Real.log M.delta|)))) :
    ∀ᵐ ω ∂(anchoredC11SampleLaw M hmeas hfull).toMeasure,
      ∀ᶠ j : ℕ in atTop, Y j ω ≤ j + 1 := by
  have hD : 0 < C * M.delta ^ 2 * |Real.log M.delta| := tail_denominator_pos M hC
  have he : 0 < (1 - gamma) ^ 2 := by
    have : 0 < 1 - gamma := by linarith
    positivity
  have hs : ∀ j : ℕ,
      (anchoredC11SampleLaw M hmeas hfull).toMeasure {ω' | j + 1 < Y j ω'} ≤
        ENNReal.ofReal
          (C * Real.exp (-((1 - gamma) ^ 2 * max ((j : ℝ) - (C - 1)) 0) /
            (C * M.delta ^ 2 * |Real.log M.delta|))) := by
    intro j
    have hcast : ((j + 1 : ℕ) : ℝ) - C = (j : ℝ) - (C - 1) := by push_cast; ring
    have h := hYtail j
    rwa [hcast] at h
  have hbc := ae_eventually_not_mem_of_expTail
    (anchoredC11SampleLaw M hmeas hfull).toMeasure hC.le hD he hs
  filter_upwards [hbc] with ω hω
  filter_upwards [hω] with j hj
  exact not_lt.1 hj

/-! ### The Liouville clause -/



theorem liouvilleClause_of_holderClause (M : GMCModel d) {C0 C : ℝ}
    (hC : 0 < C)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    (hrange : gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hholder : ∃ full : Set (AnchoredC11Sample d),
      MeasurableSet full ∧
      (anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
      ∀ L : WithTop ℕ, ∀ m : ℕ, 0 < m →
        ∃ X : AnchoredC11Sample d → ℕ,
          Measurable X ∧ (∀ ω, 0 < X ω) ∧
          (∀ k : ℕ, 0 < k →
            (anchoredC11SampleLaw M hmeas hfull).toMeasure
                {ω' | k < X ω'} ≤ ENNReal.ofReal
            (C * Real.exp (-((1 - gammaReg C0 M.delta) ^ 2 *
                max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ ω ∈ full, TheoremCInner M C L (gammaReg C0 M.delta) m X ω) :
    ∃ full : Set (AnchoredC11Sample d),
      MeasurableSet full ∧
      (anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
      ∀ ω ∈ full, ∀ L : WithTop ℕ, ∀ u : Vec d → ℝ,
        (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
          (∀ x, um.toFun x = u x) ∧
            IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) um) →
        (∀ ε > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
            sInf {r : ℝ | ∃ c : ℝ,
              r = normalizedL2On (Metric.ball (0 : Vec d) R)
                (fun x => u x - c)} < ε) →
        ∃ uRep : Vec d → ℝ,
          Continuous uRep ∧
          uRep =ᵐ[volume] u ∧
          (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
            (∀ x, um.toFun x = u x) →
            IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) um →
            uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
          ∃ c : ℝ, ∀ x, uRep x = c := by
  classical
  obtain ⟨full1, hfm1, hff1, hclause⟩ := hholder
  choose X hXmeas hXpos hXtail hXinner using hclause
  set gamma : ℝ := gammaReg C0 M.delta with hgammadef
  -- A cutoff-and-scale indexed minimal scale with no proof argument.
  set Xf : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ :=
    fun L m ↦ if h : 0 < m then X L m h else fun _ ↦ 1 with hXfdef
  have hXf : ∀ (L : WithTop ℕ) (m : ℕ) (hm : 0 < m), Xf L m = X L m hm := by
    intro L m hm
    simp only [hXfdef, dif_pos hm]
  -- S7, one probability-one event per `(L, n)`.
  have hBC : ∀ p : WithTop ℕ × ℕ,
      ∃ E : Set (AnchoredC11Sample d), MeasurableSet E ∧
        (anchoredC11SampleLaw M hmeas hfull).toMeasure E = 1 ∧
        ∀ ω ∈ E, ∀ᶠ j : ℕ in atTop, Xf p.1 (p.2 + j + 1) ω ≤ j + 1 := by
    rintro ⟨L, n⟩
    refine exists_measurable_full_of_ae _
      (ae_eventually_minimalScale_le M hmeas hfull hC hrange.2
        (Y := fun j ω ↦ Xf L (n + j + 1) ω) ?_)
    intro j
    have h := hXtail L (n + j + 1) (Nat.succ_pos _) (j + 1) (Nat.succ_pos j)
    rwa [← hXf L (n + j + 1) (Nat.succ_pos _)] at h
  obtain ⟨E, hEm, hEf, hEp⟩ :=
    exists_measurable_full_forall
      (anchoredC11SampleLaw M hmeas hfull).toMeasure hBC
  have hcompl : (anchoredC11SampleLaw M hmeas hfull).toMeasure
      ((full1 ∩ E)ᶜ) = 0 := by
    rw [Set.compl_inter]
    exact measure_union_null ((prob_compl_eq_zero_iff hfm1).2 hff1)
      ((prob_compl_eq_zero_iff hEm).2 hEf)
  refine ⟨full1 ∩ E, hfm1.inter hEm,
    (prob_compl_eq_zero_iff (hfm1.inter hEm)).1 hcompl, ?_⟩
  intro ω hω L u hw hfreq
  obtain ⟨hωfull, hωE⟩ := hω
  -- The four integrability inputs, from the clause's own `H¹` witnesses.
  obtain ⟨_, huInt, huSq, hball, hcent⟩ :=
    liouville_integrability_of_witnesses
      (fun m ↦ ⟨(hw m).choose, (hw m).choose_spec.1⟩)
  -- The display, at every inner scale and every large outer scale.
  have hdisplay : ∀ n : ℕ, ∃ N : ℤ, ∀ m : ℤ, N ≤ m →
      normalizedL2On (cube d (n : ℤ))
          (fun x ↦ u x - averageOn (cube d (n : ℤ)) u) ≤
        C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - ((n : ℤ) : ℝ))) *
          normalizedL2On (cube d m)
            (fun x ↦ u x - averageOn (cube d m) u) := by
    intro n
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hEp ω hωE (L, n))
    refine ⟨((n + J + 1 : ℕ) : ℤ), fun m hm ↦ ?_⟩
    set mm : ℕ := m.toNat with hmmdef
    have hmnn : (0 : ℤ) ≤ m := le_trans (by positivity) hm
    have hmeq : ((mm : ℕ) : ℤ) = m := Int.toNat_of_nonneg hmnn
    have hmmge : n + J + 1 ≤ mm := by omega
    have hmmpos : 0 < mm := by omega
    set j : ℕ := mm - n - 1 with hjdef
    have hjJ : J ≤ j := by omega
    have hnj : n + j + 1 = mm := by omega
    have hXle : X L mm hmmpos ω ≤ mm - n := by
      have h := hJ j hjJ
      simp only at h
      rw [hnj, hXf L mm hmmpos] at h
      omega
    obtain ⟨um, humf, humh⟩ := hw ((mm : ℕ) : ℤ)
    have hinner := hXinner L mm hmmpos ω hωfull um humh
    have hcond : ((n : ℕ) : ℤ) ≤
        ((mm : ℕ) : ℤ) - ((X L mm hmmpos ω : ℕ) : ℤ) := by omega
    have hsub : translatedCube d ((n : ℕ) : ℤ) (0 : Vec d) ⊆
        cube d (((mm : ℕ) : ℤ) - 1) := by
      rw [translatedCube_zero_eq_cube]
      exact Section6ExcessDecay.cube_subset_cube_of_le (by omega)
    have hrow := (hinner n hcond (0 : Vec d) (onTriadicGrid_zero n) hsub).1
    rw [translatedCube_zero_eq_cube] at hrow
    have hufun : um.toFun = u := funext humf
    rw [hufun] at hrow
    rw [← hmeq]
    have hcast : ((mm : ℕ) : ℝ) = (((mm : ℕ) : ℤ) : ℝ) := by push_cast; ring
    rw [hcast] at hrow
    exact hrow
  exact liouville_representative_of_natDisplays
    (lt_trans (by norm_num) hrange.1) hC.le hfreq huInt huSq hball hcent
    hdisplay (fun m um ↦ IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) um)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
