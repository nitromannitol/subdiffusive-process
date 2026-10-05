module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDDiameterTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalPercolationV2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarCycleBoundary

@[expose] public section

/-! # Conditional assembly of percolation geometry

`exists_aeASDGeometryInput_of_crossingChemical` combines the diameter tail
with the crossing-density and chemical-distance clauses supplied by
`ASDCrossingChemicalInput`. The combined nonnegative witness has the form
`H_ASD + H_res - 1`; its expectation bound uses `ogammaLE_add_of_nonneg`.
The named hypothesis is explicit in these helper statements. The final
percolation export has its own provider; this conditional assembly does not
state the status of that export. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## Two `O_{Γ₁}` combinators -/

/-- Scale monotonicity of `SubdiffusiveProcess.OGammaLE` at `σ = 1`, with no measurability side
condition: the two integrands differ by a fixed real power. -/
theorem ogammaLE_mono_scale_one' [MeasurableSpace Ω] {mu : Measure Ω} {A B : ℝ}
    {X : Ω → ℝ} (hA : 0 < A) (hAB : A ≤ B) (h : SubdiffusiveProcess.OGammaLE mu 1 A X) :
    SubdiffusiveProcess.OGammaLE mu 1 B X := by
  obtain ⟨hint, hbound⟩ := h
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hkey : ∀ ω, Real.exp ((B⁻¹ * max (X ω) 0) ^ (1 : ℝ)) =
      (Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ))) ^ (A / B) := by
    intro ω
    rw [Real.rpow_one, Real.rpow_one, ← Real.exp_mul]
    congr 1
    field_simp
  have hone : ∀ ω, (1 : ℝ) ≤ Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ)) := by
    intro ω
    rw [Real.rpow_one, Real.one_le_exp_iff]
    exact mul_nonneg (inv_nonneg.mpr hA.le) (le_max_right _ _)
  have hle : ∀ ω, Real.exp ((B⁻¹ * max (X ω) 0) ^ (1 : ℝ)) ≤
      Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ)) := by
    intro ω
    rw [hkey ω]
    calc (Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ))) ^ (A / B)
        ≤ (Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ))) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (hone ω) ((div_le_one hB).mpr hAB)
      _ = _ := Real.rpow_one _
  have hmeas : AEStronglyMeasurable
      (fun ω => Real.exp ((B⁻¹ * max (X ω) 0) ^ (1 : ℝ))) mu := by
    simp only [hkey]
    exact (hint.1.aemeasurable.pow_const (A / B)).aestronglyMeasurable
  have hint2 : Integrable (fun ω => Real.exp ((B⁻¹ * max (X ω) 0) ^ (1 : ℝ))) mu := by
    refine hint.mono' hmeas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hle ω
  exact ⟨hint2, (integral_mono hint2 hint hle).trans hbound⟩

/-- **The sum of two nonnegative `O_{Γ₁}(A)` observables is `O_{Γ₁}(2A)`.**
The pointwise step is AM–GM: `√a √b ≤ (a + b) / 2`. -/
theorem ogammaLE_add_of_nonneg [MeasurableSpace Ω] {mu : Measure Ω} {A : ℝ}
    (hA : 0 < A) {X Y : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hX : SubdiffusiveProcess.OGammaLE mu 1 A X) (hY : SubdiffusiveProcess.OGammaLE mu 1 A Y) :
    SubdiffusiveProcess.OGammaLE mu 1 (2 * A) (fun ω => X ω + Y ω) := by
  obtain ⟨hintX, hboundX⟩ := hX
  obtain ⟨hintY, hboundY⟩ := hY
  have hkey : ∀ ω, Real.exp (((2 * A)⁻¹ * max (X ω + Y ω) 0) ^ (1 : ℝ)) =
      (Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ))) ^ ((1 : ℝ) / 2) *
        (Real.exp ((A⁻¹ * max (Y ω) 0) ^ (1 : ℝ))) ^ ((1 : ℝ) / 2) := by
    intro ω
    rw [Real.rpow_one, Real.rpow_one, Real.rpow_one, ← Real.exp_mul, ← Real.exp_mul,
      ← Real.exp_add, max_eq_left (by linarith [hX0 ω, hY0 ω] : (0 : ℝ) ≤ X ω + Y ω),
      max_eq_left (hX0 ω), max_eq_left (hY0 ω)]
    congr 1
    field_simp
  have hdombound : ∀ ω, Real.exp (((2 * A)⁻¹ * max (X ω + Y ω) 0) ^ (1 : ℝ)) ≤
      (Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ)) +
        Real.exp ((A⁻¹ * max (Y ω) 0) ^ (1 : ℝ))) / 2 := by
    intro ω
    rw [hkey ω, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have ha : (0 : ℝ) ≤ Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ)) := (Real.exp_pos _).le
    have hb : (0 : ℝ) ≤ Real.exp ((A⁻¹ * max (Y ω) 0) ^ (1 : ℝ)) := (Real.exp_pos _).le
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      sq_nonneg (Real.sqrt (Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ))) -
        Real.sqrt (Real.exp ((A⁻¹ * max (Y ω) 0) ^ (1 : ℝ))))]
  have hdom : Integrable (fun ω =>
      (Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ)) +
        Real.exp ((A⁻¹ * max (Y ω) 0) ^ (1 : ℝ))) / 2) mu := (hintX.add hintY).div_const 2
  have hmeas : AEStronglyMeasurable
      (fun ω => Real.exp (((2 * A)⁻¹ * max (X ω + Y ω) 0) ^ (1 : ℝ))) mu := by
    simp only [hkey]
    exact ((hintX.1.aemeasurable.pow_const ((1 : ℝ) / 2)).mul
      (hintY.1.aemeasurable.pow_const ((1 : ℝ) / 2))).aestronglyMeasurable
  have hint2 : Integrable
      (fun ω => Real.exp (((2 * A)⁻¹ * max (X ω + Y ω) 0) ^ (1 : ℝ))) mu := by
    refine hdom.mono' hmeas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hdombound ω
  refine ⟨hint2, ?_⟩
  have hmono := integral_mono hint2 hdom hdombound
  rw [integral_div, integral_add hintX hintY] at hmono
  linarith

/-! ## Monotonicity of clause (ii) in the witness -/

theorem badComponentDiameterBound_mono_h {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {ω : Ω}
    {z : Lattice d} {C q : ℝ} {h h' : ℕ} (hh : h ≤ h') (hC : 0 ≤ C) (hq : 0 < q)
    (hb : BadComponentDiameterBound E Cbox J ω z C q h) :
    BadComponentDiameterBound E Cbox J ω z C q h' := by
  intro s hs v hv hbad a ha b hb2 i
  refine (hb s hs v hv hbad a ha b hb2 i).trans ?_
  have hcast : (h : ℝ) ≤ (h' : ℝ) := by exact_mod_cast hh
  have hlog : 0 ≤ q⁻¹ * Real.log (2 + s) :=
    mul_nonneg (inv_nonneg.mpr hq.le) (Real.log_nonneg (by linarith))
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2) hC

/-! ## The residual: clauses (i) and (iii) -/

/-- **The exact residual of the percolation anchor after the geometric estimates.**

`AEASDGeometryInput` with the clause-(ii) conjunct deleted: the crossing density
of `[ASD, Lemma B.1(2)]` and the dyadic chemical-distance thresholds of
`[DRS, Theorem 1.3]`, each with its own minimal scale and `O_{Γ₁}(C/q)` tail.
Clause (ii) is **proved** in `Section9ChemicalASDDiameterTail` and is therefore
absent here. -/
def ASDCrossingChemicalInput (dim Cdep q0 L0 Cbox J : ℕ)
    (Cprob cprob c C Clen : ℝ) : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice dim → Set Omega) (q : ℝ),
    (q0 : ℝ) ≤ q →
    (∀ j z, mu (E j z) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
    IndependentEventScales mu E →
    MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
    TranslationInvariantEventLaw mu E →
    ∃ crossing component : Lattice dim → Omega → ℕ,
      (∀ z omega, 1 ≤ crossing z omega) ∧
      (∀ z omega, 1 ≤ component z omega) ∧
      (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
      (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
      ∀ᵐ omega ∂mu,
        (∀ (z : Lattice dim), ∀ l : ℕ, crossing z omega ≤ l →
          ∀ path : List (Lattice dim), IsJStepListPath J path →
          (∃ v ∈ path, InLatticeBallReal z v (l / 3 : ℝ)) →
          (∃ v ∈ path, ¬ InLatticeBallReal z v (2 * l / 3 : ℝ)) →
          ∃ chosen : List (Lattice dim),
            chosen.Sublist path ∧ c * l ≤ chosen.length ∧
              (∀ v ∈ chosen,
                IsPercolationGoodSite E Cbox omega v ∧
                  latticeBallSet v Cbox ⊆
                    latticeBallSet z (3 * l / 4 : ℝ) \ latticeBallSet z (l / 4 : ℝ)) ∧
              chosen.Pairwise fun v w ↦
                Disjoint (latticeBallSet v Cbox) (latticeBallSet w Cbox)) ∧
        (∀ (z : Lattice dim) (n : ℕ), component z omega ≤ n →
          omega ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n))

/-! ## The reduction -/

/-- **`[ASD, Lemma B.1]` from the residual alone.**  Clause (ii) is supplied by
`Section9ChemicalASDDiameterTail`; the two witnesses are merged additively and
the amplitude doubles. -/
theorem exists_aeASDGeometryInput_of_crossingChemical (d Cdep q0r L0 Cbox : ℕ)
    (Cprob cprob c Cr Clen : ℝ)
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob)
    (hCr : 0 < Cr)
    (hres : ASDCrossingChemicalInput d Cdep q0r L0 Cbox
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
      Cprob cprob c Cr Clen) :
    ∃ q0 : ℕ, ∃ C : ℝ, 0 < C ∧ Real.log 2 ≤ C ∧ 2 * Clen ≤ C ∧
      AEASDGeometryInput d Cdep q0 L0 Cbox
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
        Cprob cprob c C Clen := by
  classical
  obtain ⟨q0g, Cgeom, hCgeompos, hclause2⟩ :=
    exists_asd_clause_two d Cbox Cdep Cprob cprob hdim hCbox hCprob hcprob
  set M : ℝ := max Cr Cgeom with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le hCr (le_max_left _ _)
  set C : ℝ := max (2 * M) (max (Real.log 2) (2 * Clen)) with hCdef
  have hCM : 2 * M ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith) hCM
  refine ⟨max 1 (max q0g q0r), C, hCpos, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _), ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw
  have hqpos : 0 < q :=
    lt_of_lt_of_le zero_lt_one (le_trans (by exact_mod_cast Nat.le_max_left 1 _) hq)
  have hq0g : (q0g : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_left q0g q0r).trans (Nat.le_max_right 1 _)) hq
  have hq0r : (q0r : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_right q0g q0r).trans (Nat.le_max_right 1 _)) hq
  obtain ⟨comp2, hcomp2one, hcomp2tail, hcomp2ae, -⟩ :=
    hclause2 mu E q hq0g hprob hsc hr hlaw
  obtain ⟨crossing, comp3, hcr1, hc31, hcrtail, hc3tail, hae⟩ :=
    hres mu E q hq0r hprob hsc hr hlaw
  have hMq : 0 < M / q := div_pos hMpos hqpos
  have hCrq : 0 < Cr / q := div_pos hCr hqpos
  have hCgq : 0 < Cgeom / q := div_pos hCgeompos hqpos
  have hMC : M ≤ C := by linarith
  have hCrC : Cr ≤ C := (le_max_left Cr Cgeom).trans hMC
  have hCgC : Cgeom ≤ C := (le_max_right Cr Cgeom).trans hMC
  refine ⟨crossing, fun z ω => comp2 z ω + comp3 z ω - 1, hcr1, ?_, ?_, ?_, ?_⟩
  · intro z ω
    show 1 ≤ comp2 z ω + comp3 z ω - 1
    have h1 := hcomp2one z ω
    have h2 := hc31 z ω
    omega
  · intro z
    exact ogammaLE_mono_scale_one' hCrq
      (div_le_div_of_nonneg_right hCrC hqpos.le) (hcrtail z)
  · intro z
    have hcast : (fun ω => ((comp2 z ω + comp3 z ω - 1 : ℕ) : ℝ) - 1) =
        fun ω => ((comp2 z ω : ℝ) - 1) + ((comp3 z ω : ℝ) - 1) := by
      funext ω
      have h1 := hcomp2one z ω
      have h2 := hc31 z ω
      have hsub : ((comp2 z ω + comp3 z ω - 1 : ℕ) : ℝ) =
          (comp2 z ω : ℝ) + (comp3 z ω : ℝ) - 1 := by
        have : (1 : ℕ) ≤ comp2 z ω + comp3 z ω := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [hsub]
      ring
    rw [hcast]
    have hX0 : ∀ ω, (0 : ℝ) ≤ (comp2 z ω : ℝ) - 1 := by
      intro ω
      have := hcomp2one z ω
      have : (1 : ℝ) ≤ (comp2 z ω : ℝ) := by exact_mod_cast this
      linarith
    have hY0 : ∀ ω, (0 : ℝ) ≤ (comp3 z ω : ℝ) - 1 := by
      intro ω
      have := hc31 z ω
      have : (1 : ℝ) ≤ (comp3 z ω : ℝ) := by exact_mod_cast this
      linarith
    have hXM := ogammaLE_mono_scale_one' hCgq
      (div_le_div_of_nonneg_right (le_max_right Cr Cgeom) hqpos.le) (hcomp2tail z)
    have hYM := ogammaLE_mono_scale_one' hCrq
      (div_le_div_of_nonneg_right (le_max_left Cr Cgeom) hqpos.le) (hc3tail z)
    have hsum := ogammaLE_add_of_nonneg hMq hX0 hY0 hXM hYM
    have h2M : 2 * (M / q) = (2 * M) / q := by ring
    rw [h2M] at hsum
    exact ogammaLE_mono_scale_one' (by positivity)
      (div_le_div_of_nonneg_right hCM hqpos.le) hsum
  · filter_upwards [hcomp2ae, hae] with ω h2 h13
    refine ⟨h13.1, fun z => ?_, fun z n hn => ?_⟩
    · refine badComponentDiameterBound_mono_h ?_ hCpos.le hqpos
        (badComponentDiameterBound_mono hCgC hqpos (h2 z))
      have hone := hc31 z ω
      omega
    · refine h13.2 z n ?_
      have := hcomp2one z ω
      omega

/-- **The version-2.1 conclusion, from the residual alone.**

The conclusion is the block of `SubdiffusiveProcess.Section9.weighted_multiscale_percolation`
verbatim.  Its only hypothesis beyond the binders is
`ASDCrossingChemicalInput`: clause (ii) — `[ASD, Lemma B.1(3)]` — no longer
appears, because `Section9ChemicalASDDiameterTail` proves it. -/
theorem weightedMultiscalePercolation_of_crossingChemical (d Cdep q0r L0 Cbox : ℕ)
    (Cprob cprob c Cr Clen : ℝ) (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox)
    (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hCr : 0 < Cr) (hc : 0 < c)
    (hL0 : 1 ≤ L0) (hClen : 0 ≤ Clen)
    (hres : ASDCrossingChemicalInput d Cdep q0r L0 Cbox
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
      Cprob cprob c Cr Clen) :
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
  obtain ⟨q0, C, hCpos, hC1, hC2, hinput⟩ :=
    exists_aeASDGeometryInput_of_crossingChemical d Cdep q0r L0 Cbox Cprob cprob c Cr Clen
      (by omega) hCbox hCprob hcprob hCr hres
  exact weightedMultiscalePercolationV2_of_aeInput d Cdep q0 L0 Cbox Cprob cprob c C Clen
    hc hCpos hL0 hClen hC1 hC2 hinput

/-! ## `[DRS]` condition S1 for the concrete field -/

/-- **S1, unconditionally, for the concrete field.**  For `2 ≤ d`, clause (ii)
(now proved) plus `[Timár, Lemma 2]` (proved in `Section9ChemicalTimarCycleBoundary`)
give the good connectivity in the double ball at almost every sample, at every
scale `L` above the explicit threshold set by the minimal scale.

This is the `S1` half of `Section9ChemicalDRSConditions`, with no external
input left. -/
theorem ae_goodConnectedInDoubleBall_of_clause_two (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 : ℕ, ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (Cgeom / q)
            (fun omega => (component z omega : ℝ) - 1)) ∧
          (∀ᵐ omega ∂mu, ∀ (z : Lattice d) (L : ℕ),
            Cgeom * (1 + (component z omega : ℝ) +
              q⁻¹ * Real.log (2 + (2 * L : ℝ))) ^ 2 ≤ (L : ℝ) / 100 →
            GoodConnectedInDoubleBall E Cbox omega z L) := by
  obtain ⟨q0, Cgeom, hCgeom, hclause2⟩ :=
    exists_asd_clause_two d Cbox Cdep Cprob cprob (by omega) hCbox hCprob hcprob
  refine ⟨q0, Cgeom, hCgeom, ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw
  obtain ⟨component, hone, htail, hae, -⟩ := hclause2 mu E q hq hprob hsc hr hlaw
  refine ⟨component, hone, htail, ?_⟩
  filter_upwards [hae] with omega homega
  intro z L hsmall
  exact goodConnectedInDoubleBall_of_badComponentDiameterBound_of_two_le hd le_rfl
    (homega z) hsmall

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
