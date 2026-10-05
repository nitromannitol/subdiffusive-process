module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalProvider
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9PercolationAlmostSure

@[expose] public section

/-!
# The almost-sure provider for the proposed version 2 of the percolation anchor

The everywhere form of
`SubdiffusiveProcess.Section9.weighted_multiscale_percolation` demands its three geometric
clauses at **every** sample while all of its hypotheses are law-level, and is
therefore false. The almost-sure form replaces the final conjunct
`FiniteRangePercolationGeometry E Cbox J c C q crossing component` by
`AEFiniteRangePercolationGeometry mu E Cbox J c C q crossing component`.

This file proves the following conditional assembly results:

* `finiteRangePercolationGeometryAt_of_chemicalDistanceThresholds` — the
  sample-wise form of `Section9ChemicalDistance`'s assembly lemma.  The existing
  assembly is already sample-wise, so this costs nothing.
* `AEASDGeometryInput` — the external `[ASD, Lemma B.1(2),(3)]` datum with its
  three geometric conjuncts quantified almost surely.  This is **strictly
  weaker** than `Section9ChemicalAssembly.ASDGeometryInput`
  (`aeASDGeometryInput_of_asdGeometryInput`), and — unlike it — it is *not*
  refuted by the Dirac counterexample of `Section9ChemicalRefutation`, whose
  bad configuration sits at a null sample.
* `weightedMultiscalePercolationV2_of_aeInput` — the version 2 conclusion,
  verbatim, from that datum.
* `AEPercolationExternalInputs` and
  `weighted_multiscale_percolation_v2_of_external`, the version 2 analogues of
  `Section9ChemicalProvider`'s pair.

The a.e.-versus-everywhere item recorded in `Section9ChemicalAssembly`'s module
docstring — `Section9ChemicalHeightTail` supplies the dyadic thresholds almost
surely while `ASDGeometryInput` asks for them at every sample — is *closed* by
version 2: `AEASDGeometryInput`'s third conjunct is exactly what the height-tail
lemma produces, and no redefinition of `component` on a null set is needed.

The concrete-field inputs include `DRSLevelData`, the P3 truncation, the seed
and crossing bounds, and the waypoint locations. The bad-site estimates use
`[ASD, Lemma B.1]`.

These are conditional assembly theorems. The source domain `d ≥ 2` (dimension-one obstruction) is now a binder of the installed
version 2.1 anchor  and of
`weighted_multiscale_percolation_v2_of_external`. This module does not
construct `AEPercolationExternalInputs` from the event-law hypotheses.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The sample-wise assembly -/

/-- **The sample-wise form of the geometry assembly.**  At a fixed sample the three
clauses are assembled exactly as in
`Section9ChemicalDistance.finiteRangePercolationGeometry_of_chemicalDistanceThresholds`;
only the outer quantifier over the sample is removed. -/
theorem finiteRangePercolationGeometryAt_of_chemicalDistanceThresholds
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {Clen c C q : ℝ} {ω : Ω}
    {crossing component : Lattice d → Ω → ℕ}
    (hClen : 0 ≤ Clen) (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C)
    (hcross : ∀ z : Lattice d, ∀ l : ℕ, crossing z ω ≤ l →
      ∀ path : List (Lattice d), IsJStepListPath J path →
      (∃ v ∈ path, InLatticeBallReal z v (l / 3 : ℝ)) →
      (∃ v ∈ path, ¬InLatticeBallReal z v (2 * l / 3 : ℝ)) →
      ∃ chosen : List (Lattice d),
        chosen.Sublist path ∧ c * l ≤ chosen.length ∧
          (∀ v ∈ chosen,
            IsPercolationGoodSite E Cbox ω v ∧
              latticeBallSet v Cbox ⊆
                latticeBallSet z (3 * l / 4 : ℝ) \ latticeBallSet z (l / 4 : ℝ)) ∧
          chosen.Pairwise fun v w ↦
            Disjoint (latticeBallSet v Cbox) (latticeBallSet w Cbox))
    (hbad : ∀ z : Lattice d, ∀ s : ℝ, 0 ≤ s → ∀ v : Lattice d,
      InLatticeBallReal z v s → ¬IsPercolationGoodSite E Cbox ω v →
      HasLatticeDiameterAtMost
        (jStepComponent J {u | ¬IsPercolationGoodSite E Cbox ω u} v)
        (C * (1 + component z ω + q⁻¹ * Real.log (2 + s)) ^ 2))
    (hheight : ∀ (z : Lattice d) (n : ℕ), component z ω ≤ n →
      ω ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) :
    FiniteRangePercolationGeometryAt E Cbox J c C q crossing component ω :=
  fun z =>
    ⟨hcross z, hbad z,
      goodPathClause_of_dyadic_threshold hClen hC1 hC2 (hheight z)⟩

/-! ## The almost-sure external datum -/

/-- **`[ASD, Lemma B.1]` with almost-sure geometry.**  The two minimal scales with
their `O_Γ₁` tails, and the three sample-wise conjuncts — clause (i), clause (ii)
and the dyadic chemical thresholds — asserted at almost every sample.

This is the version 2 shape of `Section9ChemicalAssembly.ASDGeometryInput`.  It is
strictly weaker (`aeASDGeometryInput_of_asdGeometryInput`) and it is what the
tree's own ingredients actually produce: `Section9ChemicalHeightTail`'s dyadic
threshold is an almost-sure statement.

-/
def AEASDGeometryInput (dim Cdep q0 L0 Cbox J : ℕ) (Cprob cprob c C Clen : ℝ) : Prop :=
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
        (∀ (z : Lattice dim), ∀ s : ℝ, 0 ≤ s → ∀ v : Lattice dim,
          InLatticeBallReal z v s → ¬ IsPercolationGoodSite E Cbox omega v →
          HasLatticeDiameterAtMost
            (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox omega u} v)
            (C * (1 + component z omega + q⁻¹ * Real.log (2 + s)) ^ 2)) ∧
        (∀ (z : Lattice dim) (n : ℕ), component z omega ≤ n →
          omega ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n))

/-! ## The almost-sure external datum, with measurable height fields -/

/-- **`AEASDGeometryInput` with the two measurability conjuncts appended.**

The minimal-scale witnesses the tree actually builds (`crossScale`, `asdComponent`,
`chemicalComponentScale`) are ordinary `def`s and are already proved measurable, but
`AEASDGeometryInput` never states it, so a consumer that `obtain`s `crossing`/`component`
from it cannot recover the fact.  This variant carries it; `aeASDGeometryInput_of_measurable`
forgets it again, so nothing downstream of `AEASDGeometryInput` changes.

The two conjuncts are **appended at the end**, so every existing
destructuring of the first seven components keeps its meaning. -/
def AEASDGeometryInputMeasurable (dim Cdep q0 L0 Cbox J : ℕ) (Cprob cprob c C Clen : ℝ) : Prop :=
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
      (∀ᵐ omega ∂mu,
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
        (∀ (z : Lattice dim), ∀ s : ℝ, 0 ≤ s → ∀ v : Lattice dim,
          InLatticeBallReal z v s → ¬ IsPercolationGoodSite E Cbox omega v →
          HasLatticeDiameterAtMost
            (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox omega u} v)
            (C * (1 + component z omega + q⁻¹ * Real.log (2 + s)) ^ 2)) ∧
        (∀ (z : Lattice dim) (n : ℕ), component z omega ≤ n →
          omega ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n))) ∧
      (∀ z, Measurable (crossing z)) ∧
      (∀ z, Measurable (component z))

/-- The measurable datum is the plain datum. -/
theorem aeASDGeometryInput_of_measurable {dim Cdep q0 L0 Cbox J : ℕ}
    {Cprob cprob c C Clen : ℝ}
    (h : AEASDGeometryInputMeasurable dim Cdep q0 L0 Cbox J Cprob cprob c C Clen) :
    AEASDGeometryInput dim Cdep q0 L0 Cbox J Cprob cprob c C Clen := by
  intro Omega _ mu _ E q hq hprob hscales hrange hlaw
  obtain ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail, hae, -, -⟩ :=
    h mu E q hq hprob hscales hrange hlaw
  exact ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail, hae⟩


/-- The every-sample datum implies the almost-sure datum. -/
theorem aeASDGeometryInput_of_asdGeometryInput {dim Cdep q0 L0 Cbox J : ℕ}
    {Cprob cprob c C Clen : ℝ}
    (h : ASDGeometryInput dim Cdep q0 L0 Cbox J Cprob cprob c C Clen) :
    AEASDGeometryInput dim Cdep q0 L0 Cbox J Cprob cprob c C Clen := by
  intro Omega _ mu _ E q hq hprob hscales hrange hlaw
  obtain ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail, hcross, hbad, hheight⟩ :=
    h mu E q hq hprob hscales hrange hlaw
  exact ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail,
    Filter.Eventually.of_forall fun omega =>
      ⟨fun z => hcross omega z, fun z => hbad omega z, fun z => hheight omega z⟩⟩

/-! ## The version 2 conclusion -/



theorem weightedMultiscalePercolationV2_of_aeInput
    (dim Cdep q0 L0 Cbox : ℕ) (Cprob cprob c C Clen : ℝ)
    (hc : 0 < c) (hCpos : 0 < C) (hL0 : 1 ≤ L0) (hClen : 0 ≤ Clen)
    (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C)
    (hinput : AEASDGeometryInput dim Cdep q0 L0 Cbox
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps dim)
      Cprob cprob c C Clen) :
    ∃ q0' L0' Cbox' : ℕ, ∃ c' C' : ℝ,
      0 < c' ∧ 0 < C' ∧ 1 ≤ L0' ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice dim → Set Omega) (q : ℝ),
        (q0' : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice dim → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C' / q) (fun omega => (crossing z omega : ℝ) - L0')) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C' / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          AEFiniteRangePercolationGeometry mu E Cbox'
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps dim)
            c' C' q crossing component := by
  refine ⟨q0, L0, Cbox, c, C, hc, hCpos, hL0, ?_⟩
  intro Omega _ mu _ E q hq hprob hscales hrange hlaw
  obtain ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail, hae⟩ :=
    hinput mu E q hq hprob hscales hrange hlaw
  refine ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail, hc, ?_⟩
  filter_upwards [hae] with omega homega
  exact finiteRangePercolationGeometryAt_of_chemicalDistanceThresholds
    hClen hC1 hC2 homega.1 homega.2.1 homega.2.2

/-- **The version 2 conclusion, with the two measurability conjuncts appended.**

Same proof as `weightedMultiscalePercolationV2_of_aeInput`, from the measurable datum; the
frozen block is returned verbatim and the two extra facts are carried through untouched. -/
theorem weightedMultiscalePercolationV2Measurable_of_aeInput
    (dim Cdep q0 L0 Cbox : ℕ) (Cprob cprob c C Clen : ℝ)
    (hc : 0 < c) (hCpos : 0 < C) (hL0 : 1 ≤ L0) (hClen : 0 ≤ Clen)
    (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C)
    (hinput : AEASDGeometryInputMeasurable dim Cdep q0 L0 Cbox
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps dim)
      Cprob cprob c C Clen) :
    ∃ q0' L0' Cbox' : ℕ, ∃ c' C' : ℝ,
      0 < c' ∧ 0 < C' ∧ 1 ≤ L0' ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice dim → Set Omega) (q : ℝ),
        (q0' : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice dim → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C' / q) (fun omega => (crossing z omega : ℝ) - L0')) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C' / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          AEFiniteRangePercolationGeometry mu E Cbox'
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps dim)
            c' C' q crossing component ∧
          (∀ z, Measurable (crossing z)) ∧
          (∀ z, Measurable (component z)) := by
  refine ⟨q0, L0, Cbox, c, C, hc, hCpos, hL0, ?_⟩
  intro Omega _ mu _ E q hq hprob hscales hrange hlaw
  obtain ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail, hae, hcrM, hcoM⟩ :=
    hinput mu E q hq hprob hscales hrange hlaw
  refine ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail, ⟨hc, ?_⟩, hcrM, hcoM⟩
  filter_upwards [hae] with omega homega
  exact finiteRangePercolationGeometryAt_of_chemicalDistanceThresholds
    hClen hC1 hC2 homega.1 homega.2.1 homega.2.2

/-- **The external imports of version 2.**  Identical to
`PercolationExternalInputs` except that the `[ASD, Lemma B.1]` field is the
almost-sure one. -/
structure AEPercolationExternalInputs (dim Cdep q0 L0 Cbox : ℕ)
    (Cprob cprob c C Clen Centropy : ℝ) : Prop where
  /-- `[ASD, Lemma B.1(2),(3)]` with almost-sure geometry. -/
  asdGeometry : AEASDGeometryInput dim Cdep q0 L0 Cbox
    (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps dim)
    Cprob cprob c C Clen
  /-- `[DRS, Theorem 1.3]`'s level package, unchanged. -/
  drsLevelData : DRSLevelData dim Cdep q0 Cbox Cprob cprob c Clen Centropy

/-- The version 1 external inputs imply the version 2 external inputs. -/
theorem aePercolationExternalInputs_of_percolationExternalInputs
    {dim Cdep q0 L0 Cbox : ℕ} {Cprob cprob c C Clen Centropy : ℝ}
    (h : PercolationExternalInputs dim Cdep q0 L0 Cbox Cprob cprob c C Clen Centropy) :
    AEPercolationExternalInputs dim Cdep q0 L0 Cbox Cprob cprob c C Clen Centropy :=
  ⟨aeASDGeometryInput_of_asdGeometryInput h.asdGeometry, h.drsLevelData⟩



theorem weighted_multiscale_percolation_v2_of_external (d Cdep : ℕ)
    (Cprob cprob : ℝ) (_hCprob : 0 < Cprob) (_hcprob : 0 < cprob) (_hd : 2 ≤ d)
    {q0 L0 Cbox : ℕ} {c C Clen Centropy : ℝ}
    (hc : 0 < c) (hCpos : 0 < C) (hL0 : 1 ≤ L0) (hClen : 0 ≤ Clen)
    (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C)
    (h : AEPercolationExternalInputs d Cdep q0 L0 Cbox Cprob cprob c C Clen Centropy) :
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
            c C q crossing component :=
  weightedMultiscalePercolationV2_of_aeInput d Cdep q0 L0 Cbox Cprob cprob c C Clen
    hc hCpos hL0 hClen hC1 hC2 h.asdGeometry

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
