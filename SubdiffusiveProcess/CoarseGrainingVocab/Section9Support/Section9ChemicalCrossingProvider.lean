module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingClause

@[expose] public section

/-!
# The percolation anchor, reduced to the `[DRS]` chemical-distance clause alone

`Section9ChemicalASDDiameterTail` proves clause (ii) of the multiscale
percolation geometry and `Section9ChemicalCrossingClause` proves clause (i), both
unconditionally for the concrete event field.  What is left of
`AEASDGeometryInput` is clause (iii), the dyadic chemical-distance thresholds of
`[DRS, Theorem 1.3]`, isolated here as `DRSChemicalInput`.

`exists_aeASDGeometryInput_of_chemical` produces
`Section9ChemicalPercolationV2.AEASDGeometryInput` from that hypothesis alone,
and `weightedMultiscalePercolation_of_chemical` produces the installed
version-2.1 frozen conclusion verbatim.  This helper retains `DRSChemicalInput` as an explicit hypothesis;
it contains only the chemical-distance statement. The final percolation
provider is separate from this conditional assembly.

The three witnesses are merged as before: the crossing scale is clause (i)'s,
the component scale is `H_ASD + H_res - 1`, and the `O_{Γ₁}` bound of a sum of
two nonnegative `O_{Γ₁}(A)` observables is `O_{Γ₁}(2A)`
(`ogammaLE_add_of_nonneg`).



-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-- **The additive merge of two `ℕ`-valued heights is measurable.**

`ℕ × ℕ` is countable with the full power-set `σ`-algebra, so *any* map out of it is
measurable; in particular the truncated sum `(m, n) ↦ m + n - 1`. -/
theorem measurable_component_combined [MeasurableSpace Ω] {f g : Ω → ℕ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω + g ω - 1) :=
  (measurable_of_countable fun p : ℕ × ℕ => p.1 + p.2 - 1).comp (hf.prodMk hg)

/-- **The exact residual of the percolation anchor after the percolation geometry.**

`AEASDGeometryInput` with the clause-(i) and clause-(ii) conjuncts deleted: the
dyadic chemical-distance thresholds of `[DRS, Theorem 1.3]`, with their minimal
scale and `O_{Γ₁}(C/q)` tail.  Clauses (i) and (ii) are **proved** for the
concrete field (`exists_asd_clause_one`, `exists_asd_clause_two`) and are
therefore absent here.

`[DRS, Theorem 1.3]`. -/
def DRSChemicalInput (dim Cdep q0 Cbox : ℕ) (Cprob cprob C Clen : ℝ) : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice dim → Set Omega) (q : ℝ),
    (q0 : ℝ) ≤ q →
    (∀ j z, mu (E j z) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
    IndependentEventScales mu E →
    MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
    TranslationInvariantEventLaw mu E →
    ∃ component : Lattice dim → Omega → ℕ,
      (∀ z omega, 1 ≤ component z omega) ∧
      (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
      (∀ᵐ omega ∂mu, ∀ (z : Lattice dim) (n : ℕ), component z omega ≤ n →
        omega ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ∧
      ∀ z, Measurable (component z)

/-- **`[ASD, Lemma B.1]` from the chemical-distance residual alone.** -/
theorem exists_aeASDGeometryInputMeasurable_of_chemical (d Cdep q0r Cbox : ℕ)
    (Cprob cprob Cr Clen : ℝ)
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob)
    (hCr : 0 < Cr)
    (hres : DRSChemicalInput d Cdep q0r Cbox Cprob cprob Cr Clen) :
    ∃ q0 L0 : ℕ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧ Real.log 2 ≤ C ∧ 2 * Clen ≤ C ∧
      AEASDGeometryInputMeasurable d Cdep q0 L0 Cbox
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
        Cprob cprob c C Clen := by
  classical
  obtain ⟨q0c, L0c, ccross, Ccross, hccross, hCcross, hL0c, hclause1⟩ :=
    exists_asd_clause_one d Cbox Cdep
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
      Cprob cprob hCbox hcprob
  obtain ⟨q0g, Cgeom, hCgeompos, hclause2⟩ :=
    exists_asd_clause_two d Cbox Cdep Cprob cprob hdim hCbox hCprob hcprob
  set M : ℝ := max Ccross (max Cgeom Cr) with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le hCcross (le_max_left _ _)
  set C : ℝ := max (2 * M) (max (Real.log 2) (2 * Clen)) with hCdef
  have hCM : 2 * M ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith) hCM
  refine ⟨max 1 (max q0c (max q0g q0r)), L0c, ccross, C, hccross, hCpos, hL0c,
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _), ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw
  have hqpos : 0 < q :=
    lt_of_lt_of_le zero_lt_one (le_trans (by exact_mod_cast Nat.le_max_left 1 _) hq)
  have hnc : q0c ≤ max 1 (max q0c (max q0g q0r)) := by omega
  have hng : q0g ≤ max 1 (max q0c (max q0g q0r)) := by omega
  have hnr : q0r ≤ max 1 (max q0c (max q0g q0r)) := by omega
  have hq0c : (q0c : ℝ) ≤ q := le_trans (by exact_mod_cast hnc) hq
  have hq0g : (q0g : ℝ) ≤ q := le_trans (by exact_mod_cast hng) hq
  have hq0r : (q0r : ℝ) ≤ q := le_trans (by exact_mod_cast hnr) hq
  obtain ⟨crossing, hcr1, hcrtail, hcrae, hcrmeas⟩ :=
    hclause1 mu E q hq0c hprob hsc hr hlaw
  obtain ⟨comp2, hcomp2one, hcomp2tail, hcomp2ae, hcomp2meas⟩ :=
    hclause2 mu E q hq0g hprob hsc hr hlaw
  obtain ⟨comp3, hc31, hc3tail, hc3ae, hc3meas⟩ := hres mu E q hq0r hprob hsc hr hlaw
  have hMq : 0 < M / q := div_pos hMpos hqpos
  have hCcq : 0 < Ccross / q := div_pos hCcross hqpos
  have hCrq : 0 < Cr / q := div_pos hCr hqpos
  have hCgq : 0 < Cgeom / q := div_pos hCgeompos hqpos
  have hMC : M ≤ C := by linarith
  have hCcC : Ccross ≤ C := (le_max_left Ccross _).trans hMC
  have hCrC : Cr ≤ C := ((le_max_right Cgeom Cr).trans (le_max_right Ccross _)).trans hMC
  have hCgC : Cgeom ≤ C := ((le_max_left Cgeom Cr).trans (le_max_right Ccross _)).trans hMC
  refine ⟨crossing, fun z ω => comp2 z ω + comp3 z ω - 1, hcr1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z ω
    show 1 ≤ comp2 z ω + comp3 z ω - 1
    have h1 := hcomp2one z ω
    have h2 := hc31 z ω
    omega
  · intro z
    exact ogammaLE_mono_scale_one' hCcq
      (div_le_div_of_nonneg_right hCcC hqpos.le) (hcrtail z)
  · intro z
    have hcast : (fun ω => ((comp2 z ω + comp3 z ω - 1 : ℕ) : ℝ) - 1) =
        fun ω => ((comp2 z ω : ℝ) - 1) + ((comp3 z ω : ℝ) - 1) := by
      funext ω
      have h1 := hcomp2one z ω
      have h2 := hc31 z ω
      have hsub : ((comp2 z ω + comp3 z ω - 1 : ℕ) : ℝ) =
          (comp2 z ω : ℝ) + (comp3 z ω : ℝ) - 1 := by
        have hone : (1 : ℕ) ≤ comp2 z ω + comp3 z ω := by omega
        push_cast [Nat.cast_sub hone]
        ring
      rw [hsub]
      ring
    rw [hcast]
    have hX0 : ∀ ω, (0 : ℝ) ≤ (comp2 z ω : ℝ) - 1 := by
      intro ω
      have h := hcomp2one z ω
      have h' : (1 : ℝ) ≤ (comp2 z ω : ℝ) := by exact_mod_cast h
      linarith
    have hY0 : ∀ ω, (0 : ℝ) ≤ (comp3 z ω : ℝ) - 1 := by
      intro ω
      have h := hc31 z ω
      have h' : (1 : ℝ) ≤ (comp3 z ω : ℝ) := by exact_mod_cast h
      linarith
    have hXM := ogammaLE_mono_scale_one' hCgq
      (div_le_div_of_nonneg_right
        ((le_max_left Cgeom Cr).trans (le_max_right Ccross _)) hqpos.le) (hcomp2tail z)
    have hYM := ogammaLE_mono_scale_one' hCrq
      (div_le_div_of_nonneg_right
        ((le_max_right Cgeom Cr).trans (le_max_right Ccross _)) hqpos.le) (hc3tail z)
    have hsum := ogammaLE_add_of_nonneg hMq hX0 hY0 hXM hYM
    have h2M : 2 * (M / q) = (2 * M) / q := by ring
    rw [h2M] at hsum
    exact ogammaLE_mono_scale_one' (by positivity)
      (div_le_div_of_nonneg_right hCM hqpos.le) hsum
  · filter_upwards [hcrae, hcomp2ae, hc3ae] with ω h1 h2 h3
    refine ⟨h1, fun z => ?_, fun z n hn => ?_⟩
    · refine badComponentDiameterBound_mono_h ?_ hCpos.le hqpos
        (badComponentDiameterBound_mono hCgC hqpos (h2 z))
      have hone := hc31 z ω
      omega
    · refine h3 z n ?_
      have := hcomp2one z ω
      omega
  · exact hcrmeas
  · exact fun z => measurable_component_combined (hcomp2meas z) (hc3meas z)

/-- **`[ASD, Lemma B.1]` from the chemical-distance residual alone**, forgetting the
measurability of the two height fields. -/
theorem exists_aeASDGeometryInput_of_chemical (d Cdep q0r Cbox : ℕ)
    (Cprob cprob Cr Clen : ℝ)
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob)
    (hCr : 0 < Cr)
    (hres : DRSChemicalInput d Cdep q0r Cbox Cprob cprob Cr Clen) :
    ∃ q0 L0 : ℕ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧ Real.log 2 ≤ C ∧ 2 * Clen ≤ C ∧
      AEASDGeometryInput d Cdep q0 L0 Cbox
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
        Cprob cprob c C Clen := by
  obtain ⟨q0, L0, c, C, hc, hCpos, hL0, hC1, hC2, hinput⟩ :=
    exists_aeASDGeometryInputMeasurable_of_chemical d Cdep q0r Cbox Cprob cprob Cr Clen
      hdim hCbox hCprob hcprob hCr hres
  exact ⟨q0, L0, c, C, hc, hCpos, hL0, hC1, hC2, aeASDGeometryInput_of_measurable hinput⟩

/-- **The installed version-2.1 frozen conclusion, from the chemical-distance
residual alone.**

The conclusion is the block of `SubdiffusiveProcess.Frozen.Section9.weighted_multiscale_percolation`
verbatim.  Its only hypothesis beyond the frozen binders is `DRSChemicalInput`:
clauses (i) and (ii) — `[ASD, Lemma B.1(2),(3)]` — no longer appear, because
`Section9ChemicalCrossingClause` and `Section9ChemicalASDDiameterTail` prove
them. -/
theorem weightedMultiscalePercolation_of_chemical (d Cdep q0r Cbox : ℕ)
    (Cprob cprob Cr Clen : ℝ) (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox)
    (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hCr : 0 < Cr) (hClen : 0 ≤ Clen)
    (hres : DRSChemicalInput d Cdep q0r Cbox Cprob cprob Cr Clen) :
    ∃ q0 L0 Cbox : ℕ, ∃ c C : ℝ,
      0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          AEFiniteRangePercolationGeometry mu E Cbox
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
            c C q crossing component := by
  obtain ⟨q0, L0, c, C, hcpos, hCpos, hL0, hC1, hC2, hinput⟩ :=
    exists_aeASDGeometryInput_of_chemical d Cdep q0r Cbox Cprob cprob Cr Clen
      (by omega) hCbox hCprob hcprob hCr hres
  exact weightedMultiscalePercolationV2_of_aeInput d Cdep q0 L0 Cbox Cprob cprob c C Clen
    hcpos hCpos hL0 hClen hC1 hC2 hinput

/-- **The frozen block plus the two measurability facts, from the chemical-distance
residual alone.**

`weightedMultiscalePercolation_of_chemical` is untouched and keeps its exact declared type;
this companion runs the same route through the measurable package and keeps the two extra
conjuncts, appended at the end of the frozen block. -/
theorem weightedMultiscalePercolationMeasurable_of_chemical (d Cdep q0r Cbox : ℕ)
    (Cprob cprob Cr Clen : ℝ) (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox)
    (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hCr : 0 < Cr) (hClen : 0 ≤ Clen)
    (hres : DRSChemicalInput d Cdep q0r Cbox Cprob cprob Cr Clen) :
    ∃ q0 L0 Cbox : ℕ, ∃ c C : ℝ,
      0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          AEFiniteRangePercolationGeometry mu E Cbox
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
            c C q crossing component ∧
          (∀ z, Measurable (crossing z)) ∧
          (∀ z, Measurable (component z)) := by
  obtain ⟨q0, L0, c, C, hcpos, hCpos, hL0, hC1, hC2, hinput⟩ :=
    exists_aeASDGeometryInputMeasurable_of_chemical d Cdep q0r Cbox Cprob cprob Cr Clen
      (by omega) hCbox hCprob hcprob hCr hres
  exact weightedMultiscalePercolationV2Measurable_of_aeInput d Cdep q0 L0 Cbox Cprob cprob
    c C Clen hcpos hCpos hL0 hClen hC1 hC2 hinput

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
